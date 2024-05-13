/** @file clockvector.h
 *  @brief Implements a clock vector.
 */

#ifndef __CLOCKVECTOR_H__
#define __CLOCKVECTOR_H__

#include "mymemory.h"
#include "modeltypes.h"
#include "classlist.h"
#include "set"

class ClockVector {
public:
	ClockVector(ClockVector *parent = NULL, const ModelAction *act = NULL);
	~ClockVector();
	bool merge(const ClockVector *cv);
	bool minmerge(const ClockVector *cv);
	bool synchronized_since(const ModelAction *act) const;
	std::set<int> merge_changed_indexes(const ClockVector *cv);
	bool merge_single(int tid, int epoch);
	bool greater_or_equal_excl_local_clock(const ClockVector *cv, const unsigned int tid);
	bool is_null() const;
	int get_size() const;
	void update_last_rf(int rf_seq_nr);
	int last_rf_seq_nr;

	void print() const;
	modelclock_t getClock(thread_id_t thread);

	SNAPSHOTALLOC
private:
	/** @brief Holds the actual clock data, as an array. */
	modelclock_t *clock;

	/** @brief The number of threads recorded in clock (i.e., its length).  */
	int num_threads;
};

#endif	/* __CLOCKVECTOR_H__ */
