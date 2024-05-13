#include <stdatomic.h>
#include <assert.h>
#include <threads.h>
#include <stdio.h>

// Define atomic variables
atomic_int x = ATOMIC_VAR_INIT(0);
atomic_int y = ATOMIC_VAR_INIT(0);

// Define non-atomic variables for thread communication
int a = 0;
int b = 0;

// Thread function for thread1
int thread1(void* arg) {
    // Store operations with memory order specified
    atomic_store_explicit(&x, 1, memory_order_relaxed); // Write x=1
    atomic_store_explicit(&x, 2, memory_order_release); // Write x=2
    atomic_store_explicit(&y, 1, memory_order_release); // Write y=1
    a = atomic_load_explicit(&y, memory_order_acquire); // Read a=y
    return 0;
}

// Thread function for thread2
int thread2(void* arg) {
    atomic_store_explicit(&y, 2, memory_order_release); // Write y=2
    b = atomic_load_explicit(&x, memory_order_acquire); // Read b=x
    return 0;
}

// Main function
int main() {
    thrd_t t1, t2;

    // Create threads
    if (thrd_create(&t1, thread1, NULL) != thrd_success) {
        return -1; // Handle thread creation error for thread1
    }
    if (thrd_create(&t2, thread2, NULL) != thrd_success) {
        return -1; // Handle thread creation error for thread2
    }

    // Wait for threads to finish
    thrd_join(t1, NULL);
    thrd_join(t2, NULL);

    // Assert the expected value of b
    printf("Value of a: %d\n", a);
    printf("Value of b: %d\n", b);

    return 0;
}

