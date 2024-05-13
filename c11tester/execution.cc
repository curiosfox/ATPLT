#include <stdio.h>
#include <algorithm>
#include <new>
#include <stdarg.h>
#include <errno.h>
#include <chrono>

#include "model.h"
#include "execution.h"
#include "action.h"
#include "schedule.h"
#include "common.h"
#include "clockvector.h"
#include "cyclegraph.h"
#include "datarace.h"
#include "threads-model.h"
#include "bugmessage.h"
#include "history.h"
#include "fuzzer.h"
#include "newfuzzer.h"
#include "set"


#ifdef COLLECT_STAT
static unsigned int atomic_load_count = 0;
static unsigned int atomic_store_count = 0;
static unsigned int atomic_rmw_count = 0;

static unsigned int atomic_fence_count = 0;
static unsigned int atomic_lock_count = 0;
static unsigned int atomic_trylock_count = 0;
static unsigned int atomic_unlock_count = 0;
static unsigned int atomic_notify_count = 0;
static unsigned int atomic_wait_count = 0;
static unsigned int atomic_timedwait_count = 0;
#endif

/**
 * Structure for holding small ModelChecker members that should be snapshotted
 */
struct model_snapshot_members {
	model_snapshot_members() :
		/* First thread created will have id INITIAL_THREAD_ID */
		next_thread_id(INITIAL_THREAD_ID),
		used_sequence_numbers(0),
		bugs(),
		asserted(false)
	{ }

	~model_snapshot_members() {
		for (unsigned int i = 0;i < bugs.size();i++)
			delete bugs[i];
		bugs.clear();
	}

	unsigned int next_thread_id;
	modelclock_t used_sequence_numbers;
	SnapVector<bug_message *> bugs;
	/** @brief Incorrectly-ordered synchronization was made */
	bool asserted;

	SNAPSHOTALLOC
};

/** @brief Constructor */
ModelExecution::ModelExecution(ModelChecker *m, Scheduler *scheduler) :
	model(m),
	params(NULL),
	scheduler(scheduler),
	thread_map(2),	/* We'll always need at least 2 threads */
	pthread_map(0),
	pthread_counter(2),
	action_trace(),
	obj_map(),
	condvar_waiters_map(),
	obj_thrd_map(),
	obj_wr_thrd_map(),
	obj_last_sc_map(),
	mutex_map(),
	cond_map(),
	thrd_last_action(1),
	thrd_last_fence_release(),
	priv(new struct model_snapshot_members ()),
	mo_graph(new CycleGraph()),
	hb_writes(new SnapVector<ModelAction *>()),
	chain_id_to_head(),
#ifdef NEWFUZZER
	fuzzer(new NewFuzzer()),
#else
	fuzzer(new Fuzzer()),
#endif
	isfinished(false)
{
	/* Initialize a model-checker thread, for special ModelActions */
	model_thread = new Thread(get_next_id());
	add_thread(model_thread);
	fuzzer->register_engine(m, this);
	scheduler->register_engine(this);
#ifdef TLS
	pthread_key_create(&pthreadkey, tlsdestructor);
#endif
}

/** @brief Destructor */
ModelExecution::~ModelExecution()
{
	for (unsigned int i = INITIAL_THREAD_ID;i < get_num_threads();i++)
		delete get_thread(int_to_id(i));

	delete mo_graph;
	delete priv;
}

int ModelExecution::get_execution_number() const
{
	return model->get_execution_number();
}

static SnapVector<action_list_t> * get_safe_ptr_vect_action(HashTable<const void *, SnapVector<action_list_t> *, uintptr_t, 2> * hash, void * ptr)
{
	SnapVector<action_list_t> *tmp = hash->get(ptr);
	if (tmp == NULL) {
		tmp = new SnapVector<action_list_t>();
		hash->put(ptr, tmp);
	}
	return tmp;
}

static simple_action_list_t * get_safe_ptr_action(HashTable<const void *, simple_action_list_t *, uintptr_t, 2> * hash, void * ptr)
{
	simple_action_list_t *tmp = hash->get(ptr);
	if (tmp == NULL) {
		tmp = new simple_action_list_t();
		hash->put(ptr, tmp);
	}
	return tmp;
}

static SnapVector<simple_action_list_t> * get_safe_ptr_vect_action(HashTable<const void *, SnapVector<simple_action_list_t> *, uintptr_t, 2> * hash, void * ptr)
{
	SnapVector<simple_action_list_t> *tmp = hash->get(ptr);
	if (tmp == NULL) {
		tmp = new SnapVector<simple_action_list_t>();
		hash->put(ptr, tmp);
	}
	return tmp;
}

/**
 * When vectors of action lists are reallocated due to resize, the root address of
 * action lists may change. Hence we need to fix the parent pointer of the children
 * of root.
 */
static void fixup_action_list(SnapVector<action_list_t> * vec)
{
	for (uint i = 0;i < vec->size();i++) {
		action_list_t * list = &(*vec)[i];
		if (list != NULL)
			list->fixupParent();
	}
}

#ifdef COLLECT_STAT
static inline void record_atomic_stats(ModelAction * act)
{
	switch (act->get_type()) {
	case ATOMIC_WRITE:
		atomic_store_count++;
		break;
	case ATOMIC_RMW:
		atomic_rmw_count++;
		break;
	case ATOMIC_READ:
		atomic_load_count++;
		break;
	case ATOMIC_FENCE:
		atomic_fence_count++;
		break;
	case ATOMIC_LOCK:
		atomic_lock_count++;
		break;
	case ATOMIC_TRYLOCK:
		atomic_trylock_count++;
		break;
	case ATOMIC_UNLOCK:
		atomic_unlock_count++;
		break;
	case ATOMIC_NOTIFY_ONE:
	case ATOMIC_NOTIFY_ALL:
		atomic_notify_count++;
		break;
	case ATOMIC_WAIT:
		atomic_wait_count++;
		break;
	case ATOMIC_TIMEDWAIT:
		atomic_timedwait_count++;
	default:
		return;
	}
}

void print_atomic_accesses()
{
	model_print("atomic store  count: %u\n", atomic_store_count);
	model_print("atomic load   count: %u\n", atomic_load_count);
	model_print("atomic rmw    count: %u\n", atomic_rmw_count);

	model_print("atomic fence  count: %u\n", atomic_fence_count);
	model_print("atomic lock   count: %u\n", atomic_lock_count);
	model_print("atomic trylock count: %u\n", atomic_trylock_count);
	model_print("atomic unlock count: %u\n", atomic_unlock_count);
	model_print("atomic notify count: %u\n", atomic_notify_count);
	model_print("atomic wait   count: %u\n", atomic_wait_count);
	model_print("atomic timedwait count: %u\n", atomic_timedwait_count);
}
#endif
/** @return a thread ID for a new Thread */
thread_id_t ModelExecution::get_next_id()
{
	return priv->next_thread_id++;
}

/** @return the number of user threads created during this execution */
unsigned int ModelExecution::get_num_threads() const
{
	return priv->next_thread_id;
}

/** @return a sequence number for a new ModelAction */
modelclock_t ModelExecution::get_next_seq_num()
{
	return ++++priv->used_sequence_numbers;
}

/** @return a sequence number for a new ModelAction */
modelclock_t ModelExecution::get_curr_seq_num()
{
	return priv->used_sequence_numbers;
}

/** Restore the last used sequence number when actions of a thread are postponed by Fuzzer */
void ModelExecution::restore_last_seq_num()
{
	priv->used_sequence_numbers--;
}

/**
 * @brief Should the current action wake up a given thread?
 *
 * @param curr The current action
 * @param thread The thread that we might wake up
 * @return True, if we should wake up the sleeping thread; false otherwise
 */
bool ModelExecution::should_wake_up(const ModelAction * asleep) const
{
	/* The sleep is literally sleeping */
	switch (asleep->get_type()) {
		case THREAD_SLEEP:
			if (fuzzer->shouldWake(asleep))
				return true;
			break;
		case ATOMIC_WAIT:
		case ATOMIC_TIMEDWAIT:
			if (fuzzer->waitShouldWakeUp(asleep))
				return true;
			break;
		default:
			return false;
	}

	return false;
}

void ModelExecution::wake_up_sleeping_actions()
{
	for (unsigned int i = MAIN_THREAD_ID;i < get_num_threads();i++) {
		thread_id_t tid = int_to_id(i);
		if (scheduler->is_sleep_set(tid)) {
			Thread *thr = get_thread(tid);
			ModelAction * pending = thr->get_pending();
			if (should_wake_up(pending)) {
				/* Remove this thread from sleep set */
				scheduler->remove_sleep(thr);

				if (pending->is_sleep()) {
					thr->set_wakeup_state(true);
				} else if (pending->is_wait()) {
					thr->set_wakeup_state(true);
					/* Remove this thread from list of waiters */
					simple_action_list_t *waiters = get_safe_ptr_action(&condvar_waiters_map, pending->get_location());
					for (sllnode<ModelAction *> * rit = waiters->begin();rit != NULL;rit=rit->getNext()) {
						if (rit->getVal()->get_tid() == tid) {
							waiters->erase(rit);
							break;
						}
					}

					/* Set ETIMEDOUT error */
					if (pending->is_timedwait())
						thr->set_return_value(ETIMEDOUT);
				}
			}
		}
	}
}

void ModelExecution::assert_bug(const char *msg)
{
	priv->bugs.push_back(new bug_message(msg));
	set_assert();
}

/** @return True, if any bugs have been reported for this execution */
bool ModelExecution::have_bug_reports() const
{
	return priv->bugs.size() != 0;
}

SnapVector<bug_message *> * ModelExecution::get_bugs() const
{
	return &priv->bugs;
}

/**
 * Check whether the current trace has triggered an assertion which should halt
 * its execution.
 *
 * @return True, if the execution should be aborted; false otherwise
 */
bool ModelExecution::has_asserted() const
{
	return priv->asserted;
}

/**
 * Trigger a trace assertion which should cause this execution to be halted.
 * This can be due to a detected bug or due to an infeasibility that should
 * halt ASAP.
 */
void ModelExecution::set_assert()
{
	priv->asserted = true;
}

/**
 * Check if we are in a deadlock. Should only be called at the end of an
 * execution, although it should not give false positives in the middle of an
 * execution (there should be some ENABLED thread).
 *
 * @return True if program is in a deadlock; false otherwise
 */
bool ModelExecution::is_deadlocked() const
{
	bool blocking_threads = false;
	for (unsigned int i = MAIN_THREAD_ID;i < get_num_threads();i++) {
		thread_id_t tid = int_to_id(i);
		if (is_enabled(tid))
			return false;
		Thread *t = get_thread(tid);
		if (!t->is_model_thread() && t->get_pending())
			blocking_threads = true;
	}
	return blocking_threads;
}

/**
 * Check if this is a complete execution. That is, have all thread completed
 * execution (rather than exiting because sleep sets have forced a redundant
 * execution).
 *
 * @return True if the execution is complete.
 */
bool ModelExecution::is_complete_execution() const
{
	for (unsigned int i = MAIN_THREAD_ID;i < get_num_threads();i++)
		if (is_enabled(int_to_id(i)))
			return false;
	return true;
}

ModelAction * ModelExecution::convertNonAtomicStore(void * location) {
	uint64_t value = *((const uint64_t *) location);
	modelclock_t storeclock;
	thread_id_t storethread;
	getStoreThreadAndClock(location, &storethread, &storeclock);
	setAtomicStoreFlag(location);
	ModelAction * act = new ModelAction(NONATOMIC_WRITE, memory_order_release, location, value, get_thread(storethread));
	act->set_seq_number(storeclock+1);
	add_normal_write_to_lists(act);
	ModelAction *last_act = get_last_action(act->get_tid());
	if (last_act != NULL)
		act->get_cv()->merge(last_act->get_cv());

	#if defined(ORIGINAL_IMPL)
		#ifdef TIME_IT
			clock_t start_orig = clock();
		#endif
		w_modification_order(act);
		#ifdef TIME_IT
			clock_t end_orig = clock();
			orig_time += end_orig - start_orig;
		#endif
	#endif

	#ifdef OPTIMIZED_IMPL
		#ifdef TIME_IT
			clock_t start_opt = clock();
		#endif
		ModelAction *prev_write = get_last_wr_thr_obj(act->get_tid(), act->get_location());
		process_write_opt(act, prev_write, false);
		act->set_hbmo(new ClockVector(act->get_cv(), act));
		if (prev_write != NULL) {
			act->get_hbmo()->merge(prev_write->get_hbmo());
		}
		#ifdef TIME_IT
			clock_t end_opt = clock();
			opt_time += end_opt - start_opt;
		#endif
	#endif
	add_write_to_lists(act);

#ifdef NEWFUZZER
	model->get_history()->process_action(act, act->get_tid());
#endif
	return act;
}


void ModelExecution::po_propagate_hbmo(ModelAction * act, int tid, int clock, int read_seq_nr) {
	sllnode<ModelAction *> * rit;
	for (rit = act->getActionRef()->getNext(); rit != NULL;rit=rit->getNext()) {
		ModelAction * po_write = rit->getVal();
		bool changed = false;

		if (po_write->get_seq_number() > clock)
			break;

		if ((act->get_rmw_chain_id() != 0 && act->get_rmw_chain_id() == po_write->get_rmw_chain_id())) {
			continue;
		} else {
			changed = po_write->get_hbmo()->merge_single(tid, clock);
			po_write->get_hbmo()->update_last_rf(read_seq_nr);
		}
		if (!changed && !po_write->is_rmw())
			break;
	}
}

void ModelExecution::po_propagate_hbmo(ModelAction * act, int read_seq_nr) {
	sllnode<ModelAction *> * rit;
	std::set<int> merged_rmw_chains;
	for (rit = act->getActionRef()->getNext(); rit != NULL;rit=rit->getNext()) {
		ModelAction * po_write = rit->getVal();
		bool changed = false;
		if (((act->get_rmw_chain_id() != 0 && act->get_rmw_chain_id() == po_write->get_rmw_chain_id())) ||
			(po_write->get_rmw_chain_id() != 0 && merged_rmw_chains.find(po_write->get_rmw_chain_id()) != merged_rmw_chains.end())) {
			continue;
		} else {
			changed = po_write->get_hbmo()->merge(act->get_hbmo());
			po_write->get_hbmo()->update_last_rf(read_seq_nr);
		}
		if (!changed && !po_write->is_rmw())
			break;
	}
}


bool ModelExecution::r_modification_order_opt(ModelAction *curr, ModelAction *rf, bool *canprune, ModelAction * prev_same_thread) {
	int curr_tid = curr->get_tid();
	int read_tid = rf->get_tid();
	int rf_write_clock = rf->get_hbmo()->getClock(read_tid);

	if (rf->get_rmw_chain_id() != 0 && !rf->is_rmw()) {
		rf_write_clock = rf->get_seq_number();
	}

	SnapVector<action_list_t> *thrd_lists = obj_thrd_map.get(curr->get_location());
	ASSERT(curr->is_read());

	#if !defined(ORIGINAL_IMPL)
		/* Need to ensure thrd_lists is big enough because we have not added the curr actions yet.  */
		if ((int)thrd_lists->size() <= curr_tid) {
			uint oldsize = thrd_lists->size();
			thrd_lists->resize(priv->next_thread_id);
			for(uint i = oldsize;i < priv->next_thread_id;i++)
				new (&(*thrd_lists)[i]) action_list_t();
			fixup_action_list(thrd_lists);
		}
	#endif

	ClockVector * maximal_hbmo_clocks = new ClockVector();

	bool maximal_predecessor_threads[thrd_lists->size()] = {false};

	for (unsigned int i = 0; i < hb_writes->size(); i++) {
		ModelAction * last_hb_write = (*hb_writes)[i];

		if (last_hb_write != rf) {
			if (rf->get_rmw_chain_id() != 0 && last_hb_write->get_rmw_chain_id() != 0) {
				if (rf->get_rmw_chain_id() == last_hb_write->get_rmw_chain_id()) {
					if (last_hb_write->get_chain_event_order() > rf->get_chain_event_order())
						return false;
					else
						continue;
				}
			}

			if (last_hb_write->get_hbmo()->getClock(read_tid) >= rf_write_clock)
				return false;

			if (rf->is_rmw()) {
				ModelAction *rmw_chain_head = get_rmw_chain_head(rf);
				ASSERT(!(rmw_chain_head==NULL));
				if (!rmw_chain_head->equals(rf)) {
					int rmw_chain_head_clock = rmw_chain_head->get_hbmo()->getClock(rmw_chain_head->get_tid());
					if (last_hb_write->get_hbmo()->getClock(rmw_chain_head->get_tid()) >= rmw_chain_head->get_seq_number())
						return false;
				}
			}

			if (last_hb_write == get_last_wr_thr_obj(last_hb_write->get_tid(), last_hb_write->get_location()))
				maximal_predecessor_threads[last_hb_write->get_tid()] = true;
			maximal_hbmo_clocks->merge(last_hb_write->get_hbmo());
		} else {
			if (last_hb_write == get_last_wr_thr_obj(last_hb_write->get_tid(), last_hb_write->get_location())) {
				maximal_predecessor_threads[last_hb_write->get_tid()] = true;
			}
		}
	}

	if (!maximal_hbmo_clocks->is_null()) {
		std::set<unsigned int> L = {};
		for (unsigned int x = 0; x < maximal_hbmo_clocks->get_size(); x++) {
			if (!maximal_predecessor_threads[x] && maximal_hbmo_clocks->getClock(x) > curr->get_cv()->getClock(x)) {
				L.insert(x);
			}
		}

		std::set<unsigned int>::iterator it;
		std::set<unsigned int> tempL;
		bool reiterate;
		do {
			reiterate = false;
			for (it = L.begin(); it != L.end(); ++it) {
				if (maximal_hbmo_clocks->getClock(read_tid) >= rf_write_clock)
					return false;

				int last_hb_write_pred_clock = maximal_hbmo_clocks->getClock(*it);
				if (last_hb_write_pred_clock <= curr->get_cv()->getClock(*it))
					continue;

				ModelAction * last_hb_write_pred = getLWB(*it, curr->get_tid(), last_hb_write_pred_clock, curr->get_location());
				if (last_hb_write_pred != NULL) {
					std::set<int> changed_indexes = maximal_hbmo_clocks->merge_changed_indexes(last_hb_write_pred->get_hbmo());

					std::set<int>::iterator it2;
					for (it2 = changed_indexes.begin(); it2 != changed_indexes.end(); ++it2) {
						if (*it2 != *it && !maximal_predecessor_threads[*it2])
							tempL.insert(*it2);
						if (*it2 == read_tid) {
							if (maximal_hbmo_clocks->getClock(read_tid) >= rf_write_clock)
								return false;
						}
					}
				}
			}

			if (tempL.size() > 0) {
				L = tempL;
				tempL.clear();
				reiterate = true;
			}
		} while(reiterate);
	}

	rf->get_hbmo()->merge(maximal_hbmo_clocks);
	rf->get_hbmo()->update_last_rf(curr->get_seq_number());

	action_list_t *list = &(*thrd_lists)[curr->get_tid()];
	auto rit = list->end();
	if (rit != NULL) {
		if (rit->getVal()->is_read() && rit->getVal()->get_reads_from()->equals(rf)) {
			#ifdef ORIGINAL_IMPL
				ASSERT(canprune);
			#endif
			*canprune = true;
		}
	}
	return true;
}



/**
 * Processes a read model action.
 * @param curr is the read model action to process.
 * @param rf_set is the set of model actions we can possibly read from
 * @return True if the read can be pruned from the thread map list.
 */
bool ModelExecution::process_read(ModelAction *curr, SnapVector<ModelAction *> * rf_set)
{
	SnapVector<ModelAction *> * priorset = new SnapVector<ModelAction *>();
	bool hasnonatomicstore = hasNonAtomicStore(curr->get_location());

	if (hasnonatomicstore) {
		ModelAction * nonatomicstore = convertNonAtomicStore(curr->get_location());
		rf_set->push_back(nonatomicstore);

		#if defined(OPTIMIZED_IMPL)
			#ifdef TIME_IT
				clock_t start = clock();
			#endif

			if (curr->get_cv()->synchronized_since(nonatomicstore)) {
				bool same_thread_hb_write_exists = false;

				for(unsigned int i = 0; i < hb_writes->size(); i++) {
					ModelAction * last_hb_write = (*hb_writes)[i];
					if (last_hb_write->get_tid() == nonatomicstore->get_tid()) {
						same_thread_hb_write_exists = true;
						if (nonatomicstore->get_seq_number() >= last_hb_write->get_seq_number()) {
							(*hb_writes)[i] = nonatomicstore;
						}
						break;
					}
				}
				if (!same_thread_hb_write_exists) {
					hb_writes->push_back(nonatomicstore);
				}
			}

			#ifdef TIME_IT
				clock_t finish = clock();
				opt_time += finish-start;
			#endif
		#endif
	}

	ModelAction * prev_same_thread = NULL;

	#if defined(ORIGINAL_IMPL) && defined(OPTIMIZED_IMPL)
		SnapVector<action_list_t> *thrd_lists = obj_thrd_map.get(curr->get_location());
		/* Need to ensure thrd_lists is big enough because we have not added the curr actions yet.  */
		if ((int)thrd_lists->size() <= curr->get_tid()) {
			uint oldsize = thrd_lists->size();
			thrd_lists->resize(priv->next_thread_id);
			for(uint i = oldsize;i < priv->next_thread_id;i++)
				new (&(*thrd_lists)[i]) action_list_t();
			fixup_action_list(thrd_lists);
		}
	#endif

	while(true) {
		int index = fuzzer->selectWrite(curr, rf_set);
		ModelAction *rf = (*rf_set)[index];
		ASSERT(rf);
		bool canprune = false;

		#ifdef ORIGINAL_IMPL
			#ifdef TIME_IT
				clock_t start = clock();
			#endif

			bool ret_value1 = r_modification_order(curr, rf, priorset, &canprune);

			#ifdef TIME_IT
				clock_t finish = clock();
				orig_time += finish-start;
			#endif
		#endif

		#ifdef OPTIMIZED_IMPL
			#ifdef TIME_IT
				clock_t start_opt = clock();
			#endif
			bool ret_value2 = r_modification_order_opt(curr, rf, &canprune, prev_same_thread);
			#ifdef TIME_IT
				clock_t finish_opt = clock();
				opt_time += finish_opt-start_opt;
			#endif
		#endif

		bool ret_value;
		#ifdef OPTIMIZED_IMPL
			ret_value = ret_value2;
		#endif
		#ifdef ORIGINAL_IMPL
			ret_value = ret_value1;
		#endif

		if (ret_value) {
			#ifdef OPTIMIZED_IMPL
				#ifdef TIME_IT
					clock_t start_opt_prop_overhead = clock();
				#endif
				if (rf->is_rmw()) {
					if (rf->get_tid() != get_rmw_chain_head(rf)->get_tid())
						po_propagate_hbmo(get_rmw_chain_head(rf), curr->get_seq_number());
					else
						po_propagate_hbmo(rf, curr->get_seq_number());
				} else {
					po_propagate_hbmo(rf, curr->get_seq_number());
				}
				#ifdef TIME_IT
					clock_t finish_opt_prop_overhead = clock();
					opt_time += finish_opt_prop_overhead-start_opt_prop_overhead;
				#endif
			#endif

			#ifdef ORIGINAL_IMPL
				#ifdef TIME_IT
					clock_t start_mo_overhead = clock();
				#endif

				for(unsigned int i=0;i<priorset->size();i++) {
					if (rf->is_rmw()) {
						if ((*priorset)[i]->get_rmw_chain_id() == rf->get_rmw_chain_id()) {
							mo_graph->addEdge((*priorset)[i], rf);
						} else {
							mo_graph->addEdge((*priorset)[i], get_rmw_chain_head(rf));
						}
					} else {
						mo_graph->addEdge((*priorset)[i], rf);
					}
				}
				#ifdef TIME_IT
					clock_t finish_mo_overhead = clock();
					orig_time += finish_mo_overhead-start_mo_overhead;
				#endif
			#endif
			read_from(curr, rf);
			get_thread(curr)->set_return_value(rf->get_write_value());
			delete priorset;
			//Update acquire fence clock vector
			ClockVector * hbcv = get_hb_from_write(rf);

			if (hbcv != NULL)
				get_thread(curr)->get_acq_fence_cv()->merge(hbcv);

			return canprune && (curr->get_type() == ATOMIC_READ);
		}
		priorset->clear();
		(*rf_set)[index] = rf_set->back();
		rf_set->pop_back();
	}
}

ModelAction * ModelExecution::getLWB(unsigned int target_thread, unsigned int pointer_thread, unsigned int hb, void * addr) {
	SnapVector<simple_action_list_t> *thrd_lists = obj_wr_thrd_map.get(addr);
	if (thrd_lists != NULL && target_thread < thrd_lists->size()) {
		/* Iterate over actions in thread, starting from most recent */
		simple_action_list_t *list = &(*thrd_lists)[target_thread];

		if (list->size() > 0) {
			ModelAction *first_write = list->front();
			if (!(first_write->get_seq_number() <= hb))
				return NULL;
		} else
			return NULL;

		ModelAction * pointer_event = NULL;
		if (pointers.size() <= target_thread)
			pointers.resize(target_thread+1, std::unordered_map<void *, std::vector<ModelAction *>>());

		if (pointers[target_thread].find(addr) == pointers[target_thread].end() ||
			pointers[target_thread][addr].size() <= pointer_thread) {
			pointers[target_thread].insert(std::make_pair(addr, std::vector<ModelAction *>()));
		} else
			pointer_event = pointers[target_thread][addr][pointer_thread];

		if (pointer_event == NULL) {
			sllnode<ModelAction *> * rit;
			for (rit = list->end();rit != NULL;rit=rit->getPrev()) {
				ModelAction *act = rit->getVal();
				if (act->get_seq_number() <= hb) {
					pointer_event = act;
					break;
				}
			}
		} else {
			if (!(pointer_event->get_seq_number() <= hb)) {
				sllnode<ModelAction *> * rit;
				for (rit = pointer_event->getActionRef();rit != NULL;rit=rit->getPrev()) {
					ModelAction *act = rit->getVal();
					if (act->get_seq_number() <= hb) {
						pointer_event = act;
						break;
					}
				}
			} else {
				if (pointer_event->get_seq_number() == hb)
				return pointer_event;

				sllnode<ModelAction *> * rit;
				for (rit = pointer_event->getActionRef();rit != NULL;rit=rit->getNext()) {
					ModelAction *act = rit->getVal();
					if (act->get_seq_number() <= hb)
						pointer_event = act;
					else
						break;
				}
			}
		}

		if (pointers[target_thread][addr].size() <= pointer_thread)
			pointers[target_thread][addr].resize(pointer_thread+1, 0);

		pointers[target_thread][addr][pointer_thread] = pointer_event;

		return pointer_event;
	}
	return NULL;
}

/**
 * Processes a lock, trylock, or unlock model action.  @param curr is
 * the read model action to process.
 *
 * The try lock operation checks whether the lock is taken.  If not,
 * it falls to the normal lock operation case.  If so, it returns
 * fail.
 *
 * The lock operation has already been checked that it is enabled, so
 * it just grabs the lock and synchronizes with the previous unlock.
 *
 * The unlock operation has to re-enable all of the threads that are
 * waiting on the lock.
 *
 * @return True if synchronization was updated; false otherwise
 */
bool ModelExecution::process_mutex(ModelAction *curr)
{
	cdsc::mutex *mutex = curr->get_mutex();
	struct cdsc::mutex_state *state = NULL;

	if (mutex)
		state = mutex->get_state();

	switch (curr->get_type()) {
	case ATOMIC_TRYLOCK: {
		bool success = !state->locked;
		curr->set_try_lock(success);
		if (!success) {
			get_thread(curr)->set_return_value(0);
			break;
		}
		get_thread(curr)->set_return_value(1);
	}
	//otherwise fall into the lock case
	case ATOMIC_LOCK: {
		//TODO: FIND SOME BETTER WAY TO CHECK LOCK INITIALIZED OR NOT
		//if (curr->get_cv()->getClock(state->alloc_tid) <= state->alloc_clock)
		//	assert_bug("Lock access before initialization");

		// TODO: lock count for recursive mutexes
		state->locked = get_thread(curr);
		ModelAction *unlock = get_last_unlock(curr);
		//synchronize with the previous unlock statement
		if (unlock != NULL) {
			synchronize(unlock, curr);
			return true;
		}
		break;
	}
	case ATOMIC_WAIT: {
		Thread *curr_thrd = get_thread(curr);
		/* wake up the other threads */
		for (unsigned int i = MAIN_THREAD_ID;i < get_num_threads();i++) {
			Thread *t = get_thread(int_to_id(i));
			if (t->waiting_on() == curr_thrd && t->get_pending()->is_lock())
				scheduler->wake(t);
		}

		/* unlock the lock - after checking who was waiting on it */
		state->locked = NULL;

		/* disable this thread */
		simple_action_list_t * waiters = get_safe_ptr_action(&condvar_waiters_map, curr->get_location());
		waiters->push_back(curr);
		curr_thrd->set_pending(curr);	// Forbid this thread to stash a new action

		if (fuzzer->waitShouldFail(curr))		// If wait should fail spuriously,
			scheduler->add_sleep(curr_thrd);	// place this thread into THREAD_SLEEP_SET
		else
			scheduler->sleep(curr_thrd);

		break;
	}
	case ATOMIC_TIMEDWAIT: {
		Thread *curr_thrd = get_thread(curr);
		if (!fuzzer->randomizeWaitTime(curr)) {
			curr_thrd->set_return_value(ETIMEDOUT);
			return false;
		}

		/* wake up the other threads */
		for (unsigned int i = MAIN_THREAD_ID;i < get_num_threads();i++) {
			Thread *t = get_thread(int_to_id(i));
			if (t->waiting_on() == curr_thrd && t->get_pending()->is_lock())
				scheduler->wake(t);
		}

		/* unlock the lock - after checking who was waiting on it */
		state->locked = NULL;

		/* disable this thread */
		simple_action_list_t * waiters = get_safe_ptr_action(&condvar_waiters_map, curr->get_location());
		waiters->push_back(curr);
		curr_thrd->set_pending(curr);	// Forbid this thread to stash a new action
		scheduler->add_sleep(curr_thrd);
		break;
	}
	case ATOMIC_UNLOCK: {
		// TODO: lock count for recursive mutexes
		/* wake up the other threads */
		Thread *curr_thrd = get_thread(curr);
		for (unsigned int i = MAIN_THREAD_ID;i < get_num_threads();i++) {
			Thread *t = get_thread(int_to_id(i));
			if (t->waiting_on() == curr_thrd && t->get_pending()->is_lock())
				scheduler->wake(t);
		}

		/* unlock the lock - after checking who was waiting on it */
		state->locked = NULL;
		break;
	}
	case ATOMIC_NOTIFY_ALL: {
		simple_action_list_t *waiters = get_safe_ptr_action(&condvar_waiters_map, curr->get_location());
		//activate all the waiting threads
		for (sllnode<ModelAction *> * rit = waiters->begin();rit != NULL;rit=rit->getNext()) {
			Thread * thread = get_thread(rit->getVal());
			if (thread->get_state() != THREAD_COMPLETED)
				scheduler->wake(thread);
			thread->set_wakeup_state(true);
		}
		waiters->clear();
		break;
	}
	case ATOMIC_NOTIFY_ONE: {
		simple_action_list_t *waiters = get_safe_ptr_action(&condvar_waiters_map, curr->get_location());
		if (waiters->size() != 0) {
			Thread * thread = fuzzer->selectNotify(waiters);
			if (thread->get_state() != THREAD_COMPLETED)
				scheduler->wake(thread);
			thread->set_wakeup_state(true);
		}
		break;
	}

	default:
		ASSERT(0);
	}
	return false;
}


/**
 * @brief Get the last write action performed by a particular Thread
 * @param tid The thread ID of the Thread in question
 * @return The last action in the thread
 */
ModelAction * ModelExecution::get_last_wr_thr_obj(thread_id_t tid, void * location) const
{
	SnapVector<simple_action_list_t> *thrd_lists = obj_wr_thrd_map.get(location);
	if (thrd_lists != NULL && tid < thrd_lists->size()) {
		simple_action_list_t *list = &(*thrd_lists)[tid];
		if (list->size() > 0)
			return list->end()->getVal();
	}
	return NULL;
}


/**
 * @brief Get the last write performed by a particular Thread on a given location
 * @param tid The thread ID of the Thread in question
 * @param location The location in question
 * @return The last action in the thread
 */
ModelAction * ModelExecution::get_last_event_thr_obj(thread_id_t tid, void * location) const
{
	SnapVector<action_list_t> *thrd_lists = obj_thrd_map.get(location);
	if (thrd_lists != NULL && tid < thrd_lists->size()) {
		action_list_t *list = &(*thrd_lists)[tid];
		sllnode<ModelAction *> * rit;
		if (list->size() > 0)
			return list->end()->getVal();
	}
	return NULL;
}


void ModelExecution::process_write_opt(ModelAction *curr, ModelAction *prevWrite, bool set_return_value)
{
	if (curr->is_rmw()) {
		curr->get_hbmo()->merge(curr->get_cv());
	} else {
		curr->set_hbmo(new ClockVector(curr->get_cv(), curr));
	}

	if (prevWrite != NULL) {
		curr->get_hbmo()->merge(prevWrite->get_hbmo());
	}

	if (set_return_value)
		get_thread(curr)->set_return_value(VALUE_NONE);
}

/**
 * Process a write ModelAction
 * @param curr The ModelAction to process
 * @return True if the mo_graph was updated or promises were resolved
 */
void ModelExecution::process_write(ModelAction *curr)
{
	w_modification_order(curr);
	get_thread(curr)->set_return_value(VALUE_NONE);
}

/**
 * Process a fence ModelAction
 * @param curr The ModelAction to process
 * @return True if synchronization was updated
 */
void ModelExecution::process_fence(ModelAction *curr)
{
	/*
	 * fence-relaxed: no-op
	 * fence-release: only log the occurence (not in this function), for
	 *   use in later synchronization
	 * fence-acquire (this function): search for hypothetical release
	 *   sequences
	 * fence-seq-cst: MO constraints formed in {r,w}_modification_order
	 */
	if (curr->is_acquire()) {
		curr->get_cv()->merge(get_thread(curr)->get_acq_fence_cv());
	}
}

/**
 * @brief Process the current action for thread-related activity
 *
 * Performs current-action processing for a THREAD_* ModelAction. Proccesses
 * may include setting Thread status, completing THREAD_FINISH/THREAD_JOIN
 * synchronization, etc.  This function is a no-op for non-THREAD actions
 * (e.g., ATOMIC_{READ,WRITE,RMW,LOCK}, etc.)
 *
 * @param curr The current action
 * @return True if synchronization was updated or a thread completed
 */
void ModelExecution::process_thread_action(ModelAction *curr)
{
	switch (curr->get_type()) {
	case THREAD_CREATE: {
		thrd_t *thrd = (thrd_t *)curr->get_location();
		struct thread_params *params = (struct thread_params *)curr->get_value();
		Thread *th = new Thread(get_next_id(), thrd, params->func, params->arg, get_thread(curr));
		curr->set_thread_operand(th);
		add_thread(th);
		th->set_creation(curr);
		break;
	}
	case PTHREAD_CREATE: {
		(*(uint32_t *)curr->get_location()) = pthread_counter++;

		struct pthread_params *params = (struct pthread_params *)curr->get_value();
		Thread *th = new Thread(get_next_id(), NULL, params->func, params->arg, get_thread(curr));
		curr->set_thread_operand(th);
		add_thread(th);
		th->set_creation(curr);

		if ( pthread_map.size() < pthread_counter )
			pthread_map.resize( pthread_counter );
		pthread_map[ pthread_counter-1 ] = th;

		break;
	}
	case THREAD_JOIN: {
		Thread *blocking = curr->get_thread_operand();
		ModelAction *act = get_last_action(blocking->get_id());
		synchronize(act, curr);
		break;
	}
	case PTHREAD_JOIN: {
		Thread *blocking = curr->get_thread_operand();
		ModelAction *act = get_last_action(blocking->get_id());
		synchronize(act, curr);
		break;
	}

	case THREADONLY_FINISH:
	case THREAD_FINISH: {
		Thread *th = get_thread(curr);
		if (curr->get_type() == THREAD_FINISH &&
				th == model->getInitThread()) {
			th->complete();
			setFinished();
			break;
		}

		/* Wake up any joining threads */
		for (unsigned int i = MAIN_THREAD_ID;i < get_num_threads();i++) {
			Thread *waiting = get_thread(int_to_id(i));
			if (waiting->waiting_on() == th &&
					waiting->get_pending()->is_thread_join())
				scheduler->wake(waiting);
		}
		th->complete();
		break;
	}
	case THREAD_START: {
		break;
	}
	case THREAD_SLEEP: {
		Thread *th = get_thread(curr);
		th->set_pending(curr);
		scheduler->add_sleep(th);
		break;
	}
	default:
		break;
	}
}

/**
 * Initialize the current action by performing one or more of the following
 * actions, as appropriate: merging RMWR and RMWC/RMW actions,
 * manipulating backtracking sets, allocating and
 * initializing clock vectors, and computing the promises to fulfill.
 *
 * @param curr The current action, as passed from the user context; may be
 * freed/invalidated after the execution of this function, with a different
 * action "returned" its place (pass-by-reference)
 * @return True if curr is a newly-explored action; false otherwise
 */
bool ModelExecution::initialize_curr_action(ModelAction **curr)
{
	if ((*curr)->is_rmwc() || (*curr)->is_rmw()) {
		ModelAction *newcurr = process_rmw(*curr);
		delete *curr;

		*curr = newcurr;
		return false;
	} else {
		ModelAction *newcurr = *curr;

		newcurr->set_seq_number(get_next_seq_num());
		/* Always compute new clock vector */
		newcurr->create_cv(get_parent_action(newcurr->get_tid()));

		/* Assign most recent release fence */
		newcurr->set_last_fence_release(get_last_fence_release(newcurr->get_tid()));

		return true;	/* This was a new ModelAction */
	}
}

/**
 * @brief Establish reads-from relation between two actions
 *
 * Perform basic operations involved with establishing a concrete rf relation,
 * including setting the ModelAction data and checking for release sequences.
 *
 * @param act The action that is reading (must be a read)
 * @param rf The action from which we are reading (must be a write)
 *
 * @return True if this read established synchronization
 */

void ModelExecution::read_from(ModelAction *act, ModelAction *rf)
{
	ASSERT(rf);
	ASSERT(rf->is_write());

	act->set_read_from(rf);
	if (act->is_acquire()) {
		ClockVector *cv = get_hb_from_write(rf);
		if (cv == NULL)
			return;
		act->get_cv()->merge(cv);
	}
}

/**
 * @brief Synchronizes two actions
 *
 * When A synchronizes with B (or A --sw-> B), B inherits A's clock vector.
 * This function performs the synchronization as well as providing other hooks
 * for other checks along with synchronization.
 *
 * @param first The left-hand side of the synchronizes-with relation
 * @param second The right-hand side of the synchronizes-with relation
 * @return True if the synchronization was successful (i.e., was consistent
 * with the execution order); false otherwise
 */
bool ModelExecution::synchronize(const ModelAction *first, ModelAction *second)
{
	if (*second < *first) {
		ASSERT(0);	//This should not happend
		return false;
	}
	return second->synchronize_with(first);
}

/**
 * @brief Check whether a model action is enabled.
 *
 * Checks whether an operation would be successful (i.e., is a lock already
 * locked, or is the joined thread already complete).
 *
 * For yield-blocking, yields are never enabled.
 *
 * @param curr is the ModelAction to check whether it is enabled.
 * @return a bool that indicates whether the action is enabled.
 */
bool ModelExecution::check_action_enabled(ModelAction *curr) {
	switch (curr->get_type()) {
	case ATOMIC_LOCK: {
		cdsc::mutex *lock = curr->get_mutex();
		struct cdsc::mutex_state *state = lock->get_state();
		if (state->locked) {
			Thread *lock_owner = (Thread *)state->locked;
			Thread *curr_thread = get_thread(curr);
			if (lock_owner == curr_thread && state->type == PTHREAD_MUTEX_RECURSIVE) {
				return true;
			}

			return false;
		}
		break;
	}
	case THREAD_JOIN:
	case PTHREAD_JOIN: {
		Thread *blocking = curr->get_thread_operand();
		if (!blocking->is_complete()) {
			return false;
		}
		break;
	}
	case THREAD_SLEEP: {
		if (!fuzzer->shouldSleep(curr))
			return false;
		break;
	}
	default:
		return true;
	}

	return true;
}

/**
 * This is the heart of the model checker routine. It performs model-checking
 * actions corresponding to a given "current action." Among other processes, it
 * calculates reads-from relationships, updates synchronization clock vectors,
 * forms a memory_order constraints graph, and handles replay/backtrack
 * execution when running permutations of previously-observed executions.
 *
 * @param curr The current action to process
 * @return The ModelAction that is actually executed; may be different than
 * curr
 */
ModelAction * ModelExecution::check_current_action(ModelAction *curr)
{
	ASSERT(curr);
	bool newly_explored = initialize_curr_action(&curr);

	DBG();

	wake_up_sleeping_actions();

	SnapVector<ModelAction *> * rf_set = NULL;
	bool canprune = false;
	/* Build may_read_from set for newly-created actions */
	if (curr->is_read() && newly_explored) {

		#if defined(OPTIMIZED_IMPL) && !defined(ORIGINAL_IMPL)
			rf_set = build_may_read_from_opt(curr);
		#endif
		#if defined(OPTIMIZED_IMPL) && defined(ORIGINAL_IMPL)
			build_may_read_from_opt(curr);
		#endif
		#ifdef ORIGINAL_IMPL
			rf_set = build_may_read_from(curr);
		#endif

		canprune = process_read(curr, rf_set);
		delete rf_set;
	} else
		ASSERT(rf_set == NULL);

	/* Add the action to lists if not the second part of a rmw */
	if (newly_explored) {
		add_action_to_lists(curr, canprune);
	}
	#ifdef COLLECT_STAT
		record_atomic_stats(curr);
	#endif

	process_thread_action(curr);

	if (curr->is_write()) {
		#if defined(ORIGINAL_IMPL)
			#ifdef TIME_IT
				clock_t start_orig = clock();
			#endif
			process_write(curr);
			#ifdef TIME_IT
				clock_t end_orig = clock();
				orig_time += end_orig - start_orig;
			#endif
		#endif

		#ifdef OPTIMIZED_IMPL
			#ifdef TIME_IT
				clock_t start_opt = clock();
			#endif
			ModelAction *prev_write = get_last_wr_thr_obj(curr->get_tid(), curr->get_location());
			process_write_opt(curr, prev_write, true);
			#ifdef TIME_IT
				clock_t finish_opt = clock();
				opt_time += finish_opt - start_opt;
			#endif
		#endif
	}
	if (curr->is_write())
		add_write_to_lists(curr);

	if (curr->is_fence())
		process_fence(curr);

	if (curr->is_mutex_op())
		process_mutex(curr);

	return curr;
}

ModelAction * ModelExecution::get_rmw_chain_head(ModelAction *act) {
	uint chain_id = act->get_rmw_chain_id();
	if (chain_id == 0)
		return NULL;
	else {
		return chain_id_to_head[chain_id];
	}
}

void ModelExecution::set_rmw_chain_head(uint chain_id, ModelAction *act) {
	if (chain_id_to_head.size() <= chain_id)
		chain_id_to_head.resize(chain_id*2, NULL);
	chain_id_to_head[chain_id] = act;
}

ModelAction * ModelExecution::process_rmw_opt(ModelAction *lastread) {
	lastread->set_hbmo(lastread->get_reads_from()->get_hbmo());

	if (lastread->get_reads_from()->is_rmw()) {
		lastread->set_rmw_chain_id(lastread->get_reads_from()->get_rmw_chain_id());
		lastread->set_chain_event_order(lastread->get_reads_from()->get_chain_event_order() + 1);
	} else {
		lastread->get_reads_from()->set_chain_event_order(0);
		lastread->set_chain_event_order(1);
	}
	if (lastread->get_tid() != get_rmw_chain_head(lastread)->get_tid()) {
		po_propagate_hbmo(get_rmw_chain_head(lastread), lastread->get_seq_number());
	}

	lastread->get_reads_from()->set_is_tail(false);
	return lastread;
}

/** Close out a RMWR by converting previous RMWR into a RMW or READ. */
ModelAction * ModelExecution::process_rmw(ModelAction *act) {
	ModelAction *lastread = get_last_action(act->get_tid());
	lastread->process_rmw(act);

	if (act->is_rmw() && !lastread->get_reads_from()->is_rmw()) {
		rmw_chain_count++;
		lastread->get_reads_from()->set_rmw_chain_id(rmw_chain_count);
		lastread->set_rmw_chain_id(rmw_chain_count);
		set_rmw_chain_head(rmw_chain_count, lastread->get_reads_from());
	}

	#if defined(ORIGINAL_IMPL)
		#ifdef TIME_IT
			clock_t start_orig = clock();
		#endif
		if (act->is_rmw()) {
			mo_graph->addRMWEdge(lastread->get_reads_from(), lastread);
		}
		#ifdef TIME_IT
			clock_t finish_orig = clock();
			orig_time += finish_orig-start_orig;
		#endif
	#endif

	#ifdef OPTIMIZED_IMPL
		#ifdef TIME_IT
			clock_t start_opt = clock();
		#endif
		if (act->is_rmw()) {
			process_rmw_opt(lastread);
		}
		#ifdef TIME_IT
			clock_t finish_opt = clock();
			opt_time += finish_opt - start_opt;
		#endif
	#endif
	return lastread;
}

/**
 * @brief Updates the mo_graph with the constraints imposed from the current
 * read.
 *
 * Basic idea is the following: Go through each other thread and find
 * the last action that happened before our read.  Two cases:
 *
 * -# The action is a write: that write must either occur before
 * the write we read from or be the write we read from.
 * -# The action is a read: the write that that action read from
 * must occur before the write we read from or be the same write.
 *
 * @param curr The current action. Must be a read.
 * @param rf The ModelAction or Promise that curr reads from. Must be a write.
 * @param check_only If true, then only check whether the current action satisfies
 *        read modification order or not, without modifiying priorset and canprune.
 *        False by default.
 * @return True if modification order edges were added; false otherwise
 */

bool ModelExecution::r_modification_order(ModelAction *curr, const ModelAction *rf,
																					SnapVector<ModelAction *> * priorset, bool * canprune)
{
	SnapVector<action_list_t> *thrd_lists = obj_thrd_map.get(curr->get_location());
	ASSERT(curr->is_read());

	/* Last SC fence in the current thread */
	//ModelAction *last_sc_fence_local = get_last_seq_cst_fence(curr->get_tid(), NULL);

	int tid = curr->get_tid();

	#if !defined(OPTIMIZED_IMPL)
		/* Need to ensure thrd_lists is big enough because we have not added the curr actions yet.  */
		if ((int)thrd_lists->size() <= tid) {
			uint oldsize = thrd_lists->size();
			thrd_lists->resize(priv->next_thread_id);
			for(uint i = oldsize;i < priv->next_thread_id;i++)
				new (&(*thrd_lists)[i]) action_list_t();

			fixup_action_list(thrd_lists);
		}
	#endif


	ModelAction *prev_same_thread = NULL;
	/* Iterate over all threads */
	for (unsigned int i = 0;i < thrd_lists->size();i++, tid = (((unsigned int)(tid+1)) == thrd_lists->size()) ? 0 : tid + 1) {
		/* Last SC fence in thread tid */
		// ModelAction *last_sc_fence_thread_local = NULL;
		// if (i != 0)
		// 	last_sc_fence_thread_local = get_last_seq_cst_fence(int_to_id(tid), NULL);

		// /* Last SC fence in thread tid, before last SC fence in current thread */
		// ModelAction *last_sc_fence_thread_before = NULL;
		// if (last_sc_fence_local)
		// 	last_sc_fence_thread_before = get_last_seq_cst_fence(int_to_id(tid), last_sc_fence_local);

		//Only need to iterate if either hb has changed for thread in question or SC fence after last operation...
		 if (prev_same_thread != NULL && (prev_same_thread->get_cv()->getClock(tid) == curr->get_cv()->getClock(tid))) { //&&
		// 		(last_sc_fence_thread_local == NULL || *last_sc_fence_thread_local < *prev_same_thread)) {
			continue;
		// }
		}

		/* Iterate over actions in thread, starting from most recent */
		action_list_t *list = &(*thrd_lists)[tid];
		sllnode<ModelAction *> * rit;
		int r_mod_iter_count = 0;
		for (rit = list->end();rit != NULL;rit=rit->getPrev()) {
			r_mod_iter_count++;
			ModelAction *act = rit->getVal();

			/* Skip curr */
			if (act == curr)
				continue;
			/* Don't want to add reflexive edges on 'rf' */
			if (act->equals(rf)) {
				if (act->happens_before(curr))
					break;
				else
					continue;
			}

			// if (act->is_write()) {
			// 	/* C++, Section 29.3 statement 5 */
			// 	if (curr->is_seqcst() && last_sc_fence_thread_local &&
			// 			*act < *last_sc_fence_thread_local) {
			// 		if (mo_graph->checkReachable(rf, act))
			// 			return false;
			// 		priorset->push_back(act);
			// 		break;
			// 	}
			// 	/* C++, Section 29.3 statement 4 */
			// 	else if (act->is_seqcst() && last_sc_fence_local &&
			// 					 *act < *last_sc_fence_local) {
			// 		if (mo_graph->checkReachable(rf, act))
			// 			return false;
			// 		priorset->push_back(act);
			// 		break;
			// 	}
			// 	/* C++, Section 29.3 statement 6 */
			// 	else if (last_sc_fence_thread_before &&
			// 					 *act < *last_sc_fence_thread_before) {
			// 		if (mo_graph->checkReachable(rf, act))
			// 			return false;
			// 		priorset->push_back(act);
			// 		break;
			// 	}
			// }

			/*
			 * Include at most one act per-thread that "happens
			 * before" curr
			 */
			if (act->happens_before(curr)) {
				if (i==0) {
					//if (last_sc_fence_local == NULL ||
					//		(*last_sc_fence_local < *act)) {
						prev_same_thread = act;
					//}
				}
				if (act->is_write()) {
					if (mo_graph->checkReachable(rf, act)) {
						return false;
					}

					priorset->push_back(act);
				} else {
					ModelAction *prevrf = act->get_reads_from();
					if (!prevrf->equals(rf)) {
						if (mo_graph->checkReachable(rf, prevrf)) {
							return false;
						}

						priorset->push_back(prevrf);
					} else {
						if (act->get_tid() == curr->get_tid()) {
							//Can prune curr from obj list
							*canprune = true;
						}
					}
				}
				break;
			}
		}
	}
	return true;
}

/**
 * Updates the mo_graph with the constraints imposed from the current write.
 *
 * Basic idea is the following: Go through each other thread and find
 * the lastest action that happened before our write.  Two cases:
 *
 * (1) The action is a write => that write must occur before
 * the current write
 *
 * (2) The action is a read => the write that that action read from
 * must occur before the current write.
 *
 * This method also handles two other issues:
 *
 * (I) Sequential Consistency: Making sure that if the current write is
 * seq_cst, that it occurs after the previous seq_cst write.
 *
 * (II) Sending the write back to non-synchronizing reads.
 *
 * @param curr The current action. Must be a write.
 * @param send_fv A vector for stashing reads to which we may pass our future
 * value. If NULL, then don't record any future values.
 * @return True if modification order edges were added; false otherwise
 */
void ModelExecution::w_modification_order(ModelAction *curr)
{
	SnapVector<action_list_t> *thrd_lists = obj_thrd_map.get(curr->get_location());
	unsigned int i;
	ASSERT(curr->is_write());

	SnapList<ModelAction *> edgeset;

	// if (curr->is_seqcst()) {
	// 	/* We have to at least see the last sequentially consistent write,
	// 	         so we are initialized. */
	// 	ModelAction *last_seq_cst = get_last_seq_cst_write(curr);
	// 	if (last_seq_cst != NULL) {
	// 		edgeset.push_back(last_seq_cst);
	// 	}
	// 	//update map for next query
	// 	obj_last_sc_map.put(curr->get_location(), curr);
	// }

	/* Last SC fence in the current thread */
	//ModelAction *last_sc_fence_local = get_last_seq_cst_fence(curr->get_tid(), NULL);

	/* Iterate over all threads */
	for (i = 0;i < thrd_lists->size();i++) {
		/* Last SC fence in thread i, before last SC fence in current thread */
		//ModelAction *last_sc_fence_thread_before = NULL;
		//if (last_sc_fence_local && int_to_id((int)i) != curr->get_tid())
		//	last_sc_fence_thread_before = get_last_seq_cst_fence(int_to_id(i), last_sc_fence_local);

		/* Iterate over actions in thread, starting from most recent */
		action_list_t *list = &(*thrd_lists)[i];
		sllnode<ModelAction*>* rit;
		for (rit = list->end();rit != NULL;rit=rit->getPrev()) {
			ModelAction *act = rit->getVal();
			if (act == curr) {
				/*
				 * 1) If RMW and it actually read from something, then we
				 * already have all relevant edges, so just skip to next
				 * thread.
				 *
				 * 2) If RMW and it didn't read from anything, we should
				 * whatever edge we can get to speed up convergence.
				 *
				 * 3) If normal write, we need to look at earlier actions, so
				 * continue processing list.
				 */
				if (curr->is_rmw()) {
					if (curr->get_reads_from() != NULL)
						break;
					else
						continue;
				} else
					continue;
			}

			/* C++, Section 29.3 statement 7 */
			// if (last_sc_fence_thread_before && act->is_write() &&
			// 		*act < *last_sc_fence_thread_before) {
			// 	edgeset.push_back(act);
			// 	break;
			// }

			/*
			 * Include at most one act per-thread that "happens
			 * before" curr
			 */
			if (act->happens_before(curr)) {
				/*
				 * Note: if act is RMW, just add edge:
				 *   act --mo--> curr
				 * The following edge should be handled elsewhere:
				 *   readfrom(act) --mo--> act
				 */
				if (act->is_write())
					edgeset.push_back(act);
				else if (act->is_read()) {
					//if previous read accessed a null, just keep going
					edgeset.push_back(act->get_reads_from());
				}
				break;
			}
		}
	}
	mo_graph->addEdges(&edgeset, curr);

}

/**
 * Computes the clock vector that happens before propagates from this write.
 *
 * @param rf The action that might be part of a release sequence. Must be a
 * write.
 * @return ClockVector of happens before relation.
 */

ClockVector * ModelExecution::get_hb_from_write(ModelAction *rf) const {
	SnapVector<ModelAction *> * processset = NULL;
	for ( ;rf != NULL;rf = rf->get_reads_from()) {
		ASSERT(rf->is_write());
		if (!rf->is_rmw() || (rf->is_acquire() && rf->is_release()) || rf->get_rfcv() != NULL)
			break;
		if (processset == NULL)
			processset = new SnapVector<ModelAction *>();
		processset->push_back(rf);
	}

	int i = (processset == NULL) ? 0 : processset->size();

	ClockVector * vec = NULL;
	while(true) {
		if (rf->get_rfcv() != NULL) {
			vec = rf->get_rfcv();
		} else if (rf->is_acquire() && rf->is_release()) {
			vec = rf->get_cv();
		} else if (rf->is_release() && !rf->is_rmw()) {
			vec = rf->get_cv();
		} else if (rf->is_release()) {
			//have rmw that is release and doesn't have a rfcv
			(vec = new ClockVector(vec, NULL))->merge(rf->get_cv());
			rf->set_rfcv(vec);
		} else {
			//operation that isn't release
			if (rf->get_last_fence_release()) {
				if (vec == NULL)
					vec = new ClockVector(rf->get_last_fence_release()->get_cv(), NULL);
				else
					(vec=new ClockVector(vec, NULL))->merge(rf->get_last_fence_release()->get_cv());
			} else {
				if (vec == NULL) {
					if (rf->is_rmw()) {
						vec = new ClockVector(NULL, NULL);
					}
				} else {
					vec = new ClockVector(vec, NULL);
				}
			}
			rf->set_rfcv(vec);
		}
		i--;
		if (i >= 0) {
			rf = (*processset)[i];
		} else
			break;
	}
	if (processset != NULL)
		delete processset;
	return vec;
}

/**
 * Performs various bookkeeping operations for the current ModelAction. For
 * instance, adds action to the per-object, per-thread action vector and to the
 * action trace list of all thread actions.
 *
 * @param act is the ModelAction to add.
 */
void ModelExecution::add_action_to_lists(ModelAction *act, bool canprune)
{
	int tid = id_to_int(act->get_tid());
	if ((act->is_fence() && act->is_seqcst()) || act->is_unlock()) {
		simple_action_list_t *list = get_safe_ptr_action(&obj_map, act->get_location());
		act->setActionRef(list->add_back(act));
	}

	// Update action trace, a total order of all actions
	action_trace.addAction(act);


	// Update obj_thrd_map, a per location, per thread, order of actions
	SnapVector<action_list_t> *vec = get_safe_ptr_vect_action(&obj_thrd_map, act->get_location());
	if ((int)vec->size() <= tid) {
		uint oldsize = vec->size();
		vec->resize(priv->next_thread_id);
		for(uint i = oldsize;i < priv->next_thread_id;i++)
			new (&(*vec)[i]) action_list_t();

		fixup_action_list(vec);
	}
	if (!canprune && (act->is_read() || act->is_write()))
		(*vec)[tid].addAction(act);

	// Update thrd_last_action, the last action taken by each thread
	if ((int)thrd_last_action.size() <= tid)
		thrd_last_action.resize(get_num_threads());
	thrd_last_action[tid] = act;

	// Update thrd_last_fence_release, the last release fence taken by each thread
	if (act->is_fence() && act->is_release()) {
		if ((int)thrd_last_fence_release.size() <= tid)
			thrd_last_fence_release.resize(get_num_threads());
		thrd_last_fence_release[tid] = act;
	}

	if (act->is_wait()) {
		void *mutex_loc = (void *) act->get_value();
		act->setActionRef(get_safe_ptr_action(&obj_map, mutex_loc)->add_back(act));
	}
}

void insertIntoActionList(action_list_t *list, ModelAction *act) {
	list->addAction(act);
}

void insertIntoActionListAndSetCV(action_list_t *list, ModelAction *act) {
	act->create_cv(NULL);
	list->addAction(act);
}

/**
 * Performs various bookkeeping operations for a normal write.  The
 * complication is that we are typically inserting a normal write
 * lazily, so we need to insert it into the middle of lists.
 *
 * @param act is the ModelAction to add.
 */

void ModelExecution::add_normal_write_to_lists(ModelAction *act)
{
	int tid = id_to_int(act->get_tid());
	insertIntoActionListAndSetCV(&action_trace, act);

	// Update obj_thrd_map, a per location, per thread, order of actions
	SnapVector<action_list_t> *vec = get_safe_ptr_vect_action(&obj_thrd_map, act->get_location());
	if (tid >= (int)vec->size()) {
		uint oldsize =vec->size();
		vec->resize(priv->next_thread_id);
		for(uint i=oldsize;i<priv->next_thread_id;i++)
			new (&(*vec)[i]) action_list_t();

		fixup_action_list(vec);
	}
	insertIntoActionList(&(*vec)[tid],act);

	ModelAction * lastact = thrd_last_action[tid];
	// Update thrd_last_action, the last action taken by each thrad
	if (lastact == NULL || lastact->get_seq_number() == act->get_seq_number())
		thrd_last_action[tid] = act;
}


void ModelExecution::add_write_to_lists(ModelAction *write) {
	SnapVector<simple_action_list_t> *vec = get_safe_ptr_vect_action(&obj_wr_thrd_map, write->get_location());
	int tid = id_to_int(write->get_tid());
	if (tid >= (int)vec->size()) {
		uint oldsize =vec->size();
		vec->resize(priv->next_thread_id);
		for(uint i=oldsize;i<priv->next_thread_id;i++)
			new (&(*vec)[i]) simple_action_list_t();
	}
	write->setActionRef((*vec)[tid].add_back(write));
}

/**
 * @brief Get the last action performed by a particular Thread
 * @param tid The thread ID of the Thread in question
 * @return The last action in the thread
 */
ModelAction * ModelExecution::get_last_action(thread_id_t tid) const
{
	int threadid = id_to_int(tid);
	if (threadid < (int)thrd_last_action.size())
		return thrd_last_action[id_to_int(tid)];
	else
		return NULL;
}

/**
 * @brief Get the last fence release performed by a particular Thread
 * @param tid The thread ID of the Thread in question
 * @return The last fence release in the thread, if one exists; NULL otherwise
 */
ModelAction * ModelExecution::get_last_fence_release(thread_id_t tid) const
{
	int threadid = id_to_int(tid);
	if (threadid < (int)thrd_last_fence_release.size())
		return thrd_last_fence_release[id_to_int(tid)];
	else
		return NULL;
}

/**
 * Gets the last memory_order_seq_cst write (in the total global sequence)
 * performed on a particular object (i.e., memory location), not including the
 * current action.
 * @param curr The current ModelAction; also denotes the object location to
 * check
 * @return The last seq_cst write
 */
ModelAction * ModelExecution::get_last_seq_cst_write(ModelAction *curr) const
{
	void *location = curr->get_location();
	return obj_last_sc_map.get(location);
}

/**
 * Gets the last memory_order_seq_cst fence (in the total global sequence)
 * performed in a particular thread, prior to a particular fence.
 * @param tid The ID of the thread to check
 * @param before_fence The fence from which to begin the search; if NULL, then
 * search for the most recent fence in the thread.
 * @return The last prior seq_cst fence in the thread, if exists; otherwise, NULL
 */
ModelAction * ModelExecution::get_last_seq_cst_fence(thread_id_t tid, const ModelAction *before_fence) const
{
	/* All fences should have location FENCE_LOCATION */
	simple_action_list_t *list = obj_map.get(FENCE_LOCATION);

	if (!list)
		return NULL;

	sllnode<ModelAction*>* rit = list->end();

	if (before_fence) {
		for (;rit != NULL;rit=rit->getPrev())
			if (rit->getVal() == before_fence)
				break;

		ASSERT(rit->getVal() == before_fence);
		rit=rit->getPrev();
	}

	for (;rit != NULL;rit=rit->getPrev()) {
		ModelAction *act = rit->getVal();
		if (act->is_fence() && (tid == act->get_tid()) && act->is_seqcst())
			return act;
	}
	return NULL;
}

/**
 * Gets the last unlock operation performed on a particular mutex (i.e., memory
 * location). This function identifies the mutex according to the current
 * action, which is presumed to perform on the same mutex.
 * @param curr The current ModelAction; also denotes the object location to
 * check
 * @return The last unlock operation
 */
ModelAction * ModelExecution::get_last_unlock(ModelAction *curr) const
{
	void *location = curr->get_location();

	simple_action_list_t *list = obj_map.get(location);
	if (list == NULL)
		return NULL;

	/* Find: max({i in dom(S) | isUnlock(t_i) && samevar(t_i, t)}) */
	sllnode<ModelAction*>* rit;
	for (rit = list->end();rit != NULL;rit=rit->getPrev())
		if (rit->getVal()->is_unlock() || rit->getVal()->is_wait())
			return rit->getVal();
	return NULL;
}

ModelAction * ModelExecution::get_parent_action(thread_id_t tid) const
{
	ModelAction *parent = get_last_action(tid);
	if (!parent)
		parent = get_thread(tid)->get_creation();
	return parent;
}

/**
 * Returns the clock vector for a given thread.
 * @param tid The thread whose clock vector we want
 * @return Desired clock vector
 */
ClockVector * ModelExecution::get_cv(thread_id_t tid) const
{
	ModelAction *firstaction=get_parent_action(tid);
	return firstaction != NULL ? firstaction->get_cv() : NULL;
}

bool valequals(uint64_t val1, uint64_t val2, int size) {
	switch(size) {
	case 1:
		return ((uint8_t)val1) == ((uint8_t)val2);
	case 2:
		return ((uint16_t)val1) == ((uint16_t)val2);
	case 4:
		return ((uint32_t)val1) == ((uint32_t)val2);
	case 8:
		return val1==val2;
	default:
		ASSERT(0);
		return false;
	}
}

/**
 * Build up an initial set of all past writes that this 'read' action may read
 * from, as well as any previously-observed future values that must still be valid.
 *
 * @param curr is the current ModelAction that we are exploring; it must be a
 * 'read' operation.
 */
SnapVector<ModelAction *> *  ModelExecution::build_may_read_from(ModelAction *curr)
{
	#ifdef TIME_IT
		clock_t start = clock();
	#endif
	SnapVector<simple_action_list_t> *thrd_lists = obj_wr_thrd_map.get(curr->get_location());
	unsigned int i;
	ASSERT(curr->is_read());

	ModelAction *last_sc_write = NULL;

	if (curr->is_seqcst())
		last_sc_write = get_last_seq_cst_write(curr);

	SnapVector<ModelAction *> * rf_set = new SnapVector<ModelAction *>();

	/* Iterate over all threads */
	if (thrd_lists != NULL)

		for (i = 0;i < thrd_lists->size();i++) {
			/* Iterate over actions in thread, starting from most recent */
			simple_action_list_t *list = &(*thrd_lists)[i];
			sllnode<ModelAction *> * rit;

			for (rit = list->end();rit != NULL;rit=rit->getPrev()) {
				ModelAction *act = rit->getVal();

				ASSERT(act->is_write());

				if (act == curr)
					continue;

				/* Don't consider more than one seq_cst write if we are a seq_cst read. */
				bool allow_read = true;

				if (curr->is_seqcst() && (act->is_seqcst() || (last_sc_write != NULL && act->happens_before(last_sc_write))) && act != last_sc_write)
					allow_read = false;

				/* Need to check whether we will have two RMW reading from the same value */
				if (curr->is_rmwr()) {
					/* It is okay if we have a failing CAS */
					if (!curr->is_rmwrcas() ||
							valequals(curr->get_value(), act->get_value(), curr->getSize())) {
						//Need to make sure we aren't the second RMW
						CycleNode * node = mo_graph->getNode_noCreate(act);
						if (node != NULL && node->getRMW() != NULL) {
							//we are the second RMW
							allow_read = false;
						}
					}
				}

				if (allow_read) {
					/* Only add feasible reads */
					rf_set->push_back(act);
				}

				/* Include at most one act per-thread that "happens before" curr */
				if (act->happens_before(curr))
					break;
			}
		}

	#ifdef TIME_IT
		clock_t end = clock();
		orig_time += end-start;
	#endif
	return rf_set;
}

/**
 * Build up an initial set of all past writes that this 'read' action may read
 * from, as well as any previously-observed future values that must still be valid.
 *
 * @param curr is the current ModelAction that we are exploring; it must be a
 * 'read' operation.
 */
SnapVector<ModelAction *> *  ModelExecution::build_may_read_from_opt(ModelAction *curr)
{
	#ifdef TIME_IT
		clock_t start = clock();
	#endif
	#if defined(OPTIMIZED_IMPL)
		hb_writes = new SnapVector<ModelAction *>(thread_map.size());
	#endif

	SnapVector<simple_action_list_t> *thrd_lists = obj_wr_thrd_map.get(curr->get_location());
	ASSERT(curr->is_read());

	ModelAction *last_sc_write = NULL;

	if (curr->is_seqcst())
		last_sc_write = get_last_seq_cst_write(curr);

	SnapVector<ModelAction *> * rf_set = new SnapVector<ModelAction *>();
	int tid;
	unsigned int i;

	ModelAction * prev_same_thread = get_last_event_thr_obj(curr->get_tid(), curr->get_location());
	if (prev_same_thread != NULL) {
		if (prev_same_thread->is_write())
			prev_same_thread = NULL;
		else
			prev_same_thread = prev_same_thread->get_reads_from();
	}

	/* Iterate over all threads */
	if (thrd_lists != NULL) {
		tid = curr->get_tid() < thrd_lists->size() ? curr->get_tid() : 0;

	    for (i = 0;i < thrd_lists->size();i++, tid = (((unsigned int)(tid+1)) == thrd_lists->size()) ? 0 : tid + 1) {
			/* Iterate over actions in thread, starting from most recent */
			simple_action_list_t *list = &(*thrd_lists)[tid];

			sllnode<ModelAction *> * rit;

			int iter_count = 0;
			for (rit = list->end();rit != NULL;rit=rit->getPrev()) {
				iter_count++;
				ModelAction *act = rit->getVal();

				ASSERT(act->is_write());

				if (act == curr)
					continue;

				/* Don't consider more than one seq_cst write if we are a seq_cst read. */
				bool allow_read = true;

				if (curr->is_seqcst() && (act->is_seqcst() || (last_sc_write != NULL && act->happens_before(last_sc_write))) && act != last_sc_write)
					allow_read = false;

				/* Need to check whether we will have two RMW reading from the same value */
				if (curr->is_rmwr()) {
					/* It is okay if we have a failing CAS */
					if (!curr->is_rmwrcas() ||
							valequals(curr->get_value(), act->get_value(), curr->getSize())) {
						//Need to make sure we aren't the second RMW
						if (!act->get_is_tail()) {
							//we are the second RMW
							allow_read = false;
						}
					}
				}

				if (allow_read) {
					/* Only add feasible reads */
					rf_set->push_back(act);
				}

				/* Include at most one act per-thread that "happens before" curr */
				if (act->happens_before(curr)) {
					if (prev_same_thread != NULL &&
						act->get_seq_number() <= prev_same_thread->get_cv()->getClock(act->get_tid()) &&
						act->get_hbmo()->last_rf_seq_nr <= prev_same_thread->get_seq_number()) {
						break;
					}
					hb_writes->push_back(act);
					break;
				}
			}
		}
	}

	#ifdef TIME_IT
		clock_t end = clock();
		opt_time += end-start;
	#endif
	return rf_set;
}

static void print_list(action_list_t *list)
{
	sllnode<ModelAction*> *it;

	model_print("------------------------------------------------------------------------------------\n");
	model_print("#    t    Action type     MO       Location         Value               Rf  CV\n");
	model_print("------------------------------------------------------------------------------------\n");

	unsigned int hash = 0;

	for (it = list->begin();it != NULL;it=it->getNext()) {
		const ModelAction *act = it->getVal();
		if (act->get_seq_number() > 0)
			act->print();
		hash = hash^(hash<<3)^(it->getVal()->hash());
	}
	model_print("HASH %u\n", hash);
	model_print("------------------------------------------------------------------------------------\n");
}

#if SUPPORT_MOD_ORDER_DUMP
void ModelExecution::dumpGraph(char *filename)
{
	char buffer[200];
	sprintf(buffer, "%s.dot", filename);
	FILE *file = fopen(buffer, "w");
	fprintf(file, "digraph %s {\n", filename);
	mo_graph->dumpNodes(file);
	ModelAction **thread_array = (ModelAction **)model_calloc(1, sizeof(ModelAction *) * get_num_threads());

	for (sllnode<ModelAction*>* it = action_trace.begin();it != NULL;it=it->getNext()) {
		ModelAction *act = it->getVal();
		if (act->is_read()) {
			mo_graph->dot_print_node(file, act);
			mo_graph->dot_print_edge(file,
															 act->get_reads_from(),
															 act,
															 "label=\"rf\", color=red, weight=2");
		}
		if (thread_array[act->get_tid()]) {
			mo_graph->dot_print_edge(file,
															 thread_array[id_to_int(act->get_tid())],
															 act,
															 "label=\"sb\", color=blue, weight=400");
		}

		thread_array[act->get_tid()] = act;
	}
	fprintf(file, "}\n");
	model_free(thread_array);
	fclose(file);
}
#endif

/** @brief Prints an execution trace summary. */
void ModelExecution::print_summary()
{
#if SUPPORT_MOD_ORDER_DUMP
	char buffername[100];
	sprintf(buffername, "exec%04u", get_execution_number());
	mo_graph->dumpGraphToFile(buffername);
	sprintf(buffername, "graph%04u", get_execution_number());
	dumpGraph(buffername);
#endif

	model_print("Execution trace %d:", get_execution_number());
	if (scheduler->all_threads_sleeping())
		model_print(" SLEEP-SET REDUNDANT");
	if (have_bug_reports())
		model_print(" DETECTED BUG(S)");

	model_print("\n");

	print_list(&action_trace);
	model_print("\n");

}

void ModelExecution::print_tail()
{
	model_print("Execution trace %d:\n", get_execution_number());

	sllnode<ModelAction*> *it;

	model_print("------------------------------------------------------------------------------------\n");
	model_print("#    t    Action type     MO       Location         Value               Rf  CV\n");
	model_print("------------------------------------------------------------------------------------\n");

	unsigned int hash = 0;

	int length = 25;
	int counter = 0;
	SnapList<ModelAction *> list;
	for (it = action_trace.end();it != NULL;it = it->getPrev()) {
		if (counter > length)
			break;

		ModelAction * act = it->getVal();
		list.push_front(act);
		counter++;
	}

	for (it = list.begin();it != NULL;it=it->getNext()) {
		const ModelAction *act = it->getVal();
		if (act->get_seq_number() > 0)
			act->print();
		hash = hash^(hash<<3)^(it->getVal()->hash());
	}
	model_print("HASH %u\n", hash);
	model_print("------------------------------------------------------------------------------------\n");
}

/**
 * Add a Thread to the system for the first time. Should only be called once
 * per thread.
 * @param t The Thread to add
 */
void ModelExecution::add_thread(Thread *t)
{
	unsigned int i = id_to_int(t->get_id());
	if (i >= thread_map.size())
		thread_map.resize(i + 1);
	thread_map[i] = t;
	if (!t->is_model_thread())
		scheduler->add_thread(t);
}

/**
 * @brief Get a Thread reference by its ID
 * @param tid The Thread's ID
 * @return A Thread reference
 */
Thread * ModelExecution::get_thread(thread_id_t tid) const
{
	unsigned int i = id_to_int(tid);
	if (i < thread_map.size())
		return thread_map[i];
	return NULL;
}

/**
 * @brief Get a reference to the Thread in which a ModelAction was executed
 * @param act The ModelAction
 * @return A Thread reference
 */
Thread * ModelExecution::get_thread(const ModelAction *act) const
{
	return get_thread(act->get_tid());
}

/**
 * @brief Get a Thread reference by its pthread ID
 * @param index The pthread's ID
 * @return A Thread reference
 */
Thread * ModelExecution::get_pthread(pthread_t pid) {
	// pid 1 is reserved for the main thread, pthread ids should start from 2
	if (pid == 1)
		return get_thread(pid);

	union {
		pthread_t p;
		uint32_t v;
	} x;
	x.p = pid;
	uint32_t thread_id = x.v;

	if (thread_id < pthread_counter + 1)
		return pthread_map[thread_id];
	else
		return NULL;
}

/**
 * @brief Check if a Thread is currently enabled
 * @param t The Thread to check
 * @return True if the Thread is currently enabled
 */
bool ModelExecution::is_enabled(Thread *t) const
{
	return scheduler->is_enabled(t);
}

/**
 * @brief Check if a Thread is currently enabled
 * @param tid The ID of the Thread to check
 * @return True if the Thread is currently enabled
 */
bool ModelExecution::is_enabled(thread_id_t tid) const
{
	return scheduler->is_enabled(tid);
}

/**
 * @brief Select the next thread to execute based on the curren action
 *
 * RMW actions occur in two parts, and we cannot split them. And THREAD_CREATE
 * actions should be followed by the execution of their child thread. In either
 * case, the current action should determine the next thread schedule.
 *
 * @param curr The current action
 * @return The next thread to run, if the current action will determine this
 * selection; otherwise NULL
 */
Thread * ModelExecution::action_select_next_thread(const ModelAction *curr) const
{
	/* Do not split atomic RMW */
	if (curr->is_rmwr())
		return get_thread(curr);
	/* Follow CREATE with the created thread */
	/* which is not needed, because model.cc takes care of this */
	if (curr->get_type() == THREAD_CREATE)
		return curr->get_thread_operand();
	if (curr->get_type() == PTHREAD_CREATE) {
		return curr->get_thread_operand();
	}
	return NULL;
}

/**
 * Takes the next step in the execution, if possible.
 * @param curr The current step to take
 * @return Returns the next Thread to run, if any; NULL if this execution
 * should terminate
 */
Thread * ModelExecution::take_step(ModelAction *curr)
{
	Thread *curr_thrd = get_thread(curr);
	ASSERT(curr_thrd->get_state() == THREAD_READY);

	ASSERT(check_action_enabled(curr));	/* May have side effects? */
	curr = check_current_action(curr);
	ASSERT(curr);

	/* Process this action in ModelHistory for records */
#ifdef NEWFUZZER
	model->get_history()->process_action( curr, curr->get_tid() );
#endif
	if (curr_thrd->is_blocked() || curr_thrd->is_complete())
		scheduler->remove_thread(curr_thrd);

	return action_select_next_thread(curr);
}

/** This method removes references to an Action before we delete it. */

void ModelExecution::removeAction(ModelAction *act) {
	{
		action_trace.removeAction(act);
	}
	{
		SnapVector<action_list_t> *vec = get_safe_ptr_vect_action(&obj_thrd_map, act->get_location());
		(*vec)[act->get_tid()].removeAction(act);
	}
	if ((act->is_fence() && act->is_seqcst()) || act->is_unlock()) {
		sllnode<ModelAction *> * listref = act->getActionRef();
		if (listref != NULL) {
			simple_action_list_t *list = get_safe_ptr_action(&obj_map, act->get_location());
			list->erase(listref);
		}
	} else if (act->is_wait()) {
		sllnode<ModelAction *> * listref = act->getActionRef();
		if (listref != NULL) {
			void *mutex_loc = (void *) act->get_value();
			get_safe_ptr_action(&obj_map, mutex_loc)->erase(listref);
		}
	} else if (act->is_free()) {
		sllnode<ModelAction *> * listref = act->getActionRef();
		if (listref != NULL) {
			SnapVector<simple_action_list_t> *vec = get_safe_ptr_vect_action(&obj_wr_thrd_map, act->get_location());
			(*vec)[act->get_tid()].erase(listref);
		}

		//Clear it from last_sc_map
		if (obj_last_sc_map.get(act->get_location()) == act) {
			obj_last_sc_map.remove(act->get_location());
		}

		//Remove from Cyclegraph
		mo_graph->freeAction(act);
	}
}

/** Computes clock vector that all running threads have already synchronized to.  */

ClockVector * ModelExecution::computeMinimalCV() {
	ClockVector *cvmin = NULL;
	//Thread 0 isn't a real thread, so skip it..
	for(unsigned int i = 1;i < thread_map.size();i++) {
		Thread * t = thread_map[i];
		if (t->is_complete())
			continue;
		thread_id_t tid = int_to_id(i);
		ClockVector * cv = get_cv(tid);
		if (cvmin == NULL)
			cvmin = new ClockVector(cv, NULL);
		else
			cvmin->minmerge(cv);
	}
	return cvmin;
}


/** Sometimes we need to remove an action that is the most recent in the thread.  This happens if it is mo before action in other threads.  In that case we need to create a replacement latest ModelAction */

void ModelExecution::fixupLastAct(ModelAction *act) {
	ModelAction *newact = new ModelAction(ATOMIC_NOP, std::memory_order_seq_cst, NULL, VALUE_NONE, get_thread(act->get_tid()));
	newact->set_seq_number(get_next_seq_num());
	newact->create_cv(act);
	newact->set_last_fence_release(act->get_last_fence_release());
	add_action_to_lists(newact, false);
}

/** Compute which actions to free.  */

void ModelExecution::collectActions() {
	if (priv->used_sequence_numbers < params->traceminsize)
		return;

	//Compute minimal clock vector for all live threads
	ClockVector *cvmin = computeMinimalCV();
	SnapVector<CycleNode *> * queue = new SnapVector<CycleNode *>();
	modelclock_t maxtofree = priv->used_sequence_numbers - params->traceminsize;

	//Next walk action trace...  When we hit an action, see if it is
	//invisible (e.g., earlier than the first before the minimum
	//clock for the thread...  if so erase it and all previous
	//actions in cyclegraph
	sllnode<ModelAction*> * it;
	for (it = action_trace.begin();it != NULL;it=it->getNext()) {
		ModelAction *act = it->getVal();
		modelclock_t actseq = act->get_seq_number();

		//See if we are done
		if (actseq > maxtofree)
			break;

		thread_id_t act_tid = act->get_tid();
		modelclock_t tid_clock = cvmin->getClock(act_tid);

		//Free if it is invisible or we have set a flag to remove visible actions.
		if (actseq <= tid_clock || params->removevisible) {
			ModelAction * write;
			if (act->is_write()) {
				write = act;
			} else if (act->is_read()) {
				write = act->get_reads_from();
			} else
				continue;

			//Mark everything earlier in MO graph to be freed
			CycleNode * cn = mo_graph->getNode_noCreate(write);
			if (cn != NULL) {
				queue->push_back(cn);
				while(!queue->empty()) {
					CycleNode * node = queue->back();
					queue->pop_back();
					for(unsigned int i=0;i<node->getNumInEdges();i++) {
						CycleNode * prevnode = node->getInEdge(i);
						ModelAction * prevact = prevnode->getAction();
						if (prevact->get_type() != READY_FREE) {
							prevact->set_free();
							queue->push_back(prevnode);
						}
					}
				}
			}
		}
	}

	//We may need to remove read actions in the window we don't delete to preserve correctness.

	for (sllnode<ModelAction*> * it2 = action_trace.end();it2 != it;) {
		ModelAction *act = it2->getVal();
		//Do iteration early in case we delete the act
		it2=it2->getPrev();
		bool islastact = false;
		ModelAction *lastact = get_last_action(act->get_tid());
		if (act == lastact) {
			Thread * th = get_thread(act);
			islastact = !th->is_complete();
		}

		if (act->is_read()) {
			if (act->get_reads_from()->is_free()) {
				if (act->is_rmw()) {
					//Weaken a RMW from a freed store to a write
					act->set_type(ATOMIC_WRITE);
				} else {
					removeAction(act);
					if (islastact) {
						fixupLastAct(act);
					}

					delete act;
					continue;
				}
			}
		}
		//If we don't delete the action, we should remove references to release fences

		const ModelAction *rel_fence =act->get_last_fence_release();
		if (rel_fence != NULL) {
			modelclock_t relfenceseq = rel_fence->get_seq_number();
			thread_id_t relfence_tid = rel_fence->get_tid();
			modelclock_t tid_clock = cvmin->getClock(relfence_tid);
			//Remove references to irrelevant release fences
			if (relfenceseq <= tid_clock)
				act->set_last_fence_release(NULL);
		}
	}
	//Now we are in the window of old actions that we remove if possible
	for (;it != NULL;) {
		ModelAction *act = it->getVal();
		//Do iteration early since we may delete node...
		it=it->getPrev();
		bool islastact = false;
		ModelAction *lastact = get_last_action(act->get_tid());
		if (act == lastact) {
			Thread * th = get_thread(act);
			islastact = !th->is_complete();
		}

		if (act->is_read()) {
			if (act->get_reads_from()->is_free()) {
				if (act->is_rmw()) {
					act->set_type(ATOMIC_WRITE);
				} else {
					removeAction(act);
					if (islastact) {
						fixupLastAct(act);
					}
					delete act;
					continue;
				}
			}
		} else if (act->is_free()) {
			removeAction(act);
			if (islastact) {
				fixupLastAct(act);
			}
			delete act;
			continue;
		} else if (act->is_write()) {
			//Do nothing with write that hasn't been marked to be freed
		} else if (islastact) {
			//Keep the last action for non-read/write actions
		} else if (act->is_fence()) {
			//Note that acquire fences can always be safely
			//removed, but could incur extra overheads in
			//traversals.  Removing them before the cvmin seems
			//like a good compromise.

			//Release fences before the cvmin don't do anything
			//because everyone has already synchronized.

			//Sequentially fences before cvmin are redundant
			//because happens-before will enforce same
			//orderings.

			modelclock_t actseq = act->get_seq_number();
			thread_id_t act_tid = act->get_tid();
			modelclock_t tid_clock = cvmin->getClock(act_tid);
			if (actseq <= tid_clock) {
				removeAction(act);
				// Remove reference to act from thrd_last_fence_release
				int thread_id = id_to_int( act->get_tid() );
				if (thrd_last_fence_release[thread_id] == act) {
					thrd_last_fence_release[thread_id] = NULL;
				}
				delete act;
				continue;
			}
		} else {
			//need to deal with lock, annotation, wait, notify, thread create, start, join, yield, finish, nops
			//lock, notify thread create, thread finish, yield, finish are dead as soon as they are in the trace
			//need to keep most recent unlock/wait for each lock
			if(act->is_unlock() || act->is_wait()) {
				ModelAction * lastlock = get_last_unlock(act);
				if (lastlock != act) {
					removeAction(act);
					delete act;
					continue;
				}
			} else if (act->is_create()) {
				if (act->get_thread_operand()->is_complete()) {
					removeAction(act);
					delete act;
					continue;
				}
			} else {
				removeAction(act);
				delete act;
				continue;
			}
		}

		//If we don't delete the action, we should remove references to release fences
		const ModelAction *rel_fence =act->get_last_fence_release();
		if (rel_fence != NULL) {
			modelclock_t relfenceseq = rel_fence->get_seq_number();
			thread_id_t relfence_tid = rel_fence->get_tid();
			modelclock_t tid_clock = cvmin->getClock(relfence_tid);
			//Remove references to irrelevant release fences
			if (relfenceseq <= tid_clock)
				act->set_last_fence_release(NULL);
		}
	}

	delete cvmin;
	delete queue;
}

Fuzzer * ModelExecution::getFuzzer() {
	return fuzzer;
}
