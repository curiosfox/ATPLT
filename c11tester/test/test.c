#include <stdio.h>
#include <stdlib.h>
#include <pthread.h>
#include <stdatomic.h>

atomic_int x = ATOMIC_VAR_INIT(0);
atomic_int y = ATOMIC_VAR_INIT(0);
int a = 0;
int b = 0;

void* thread1_func(void* arg) {
    atomic_store(&x, 1);
    atomic_store(&y, 1);
    atomic_store(&x, 2);
    return NULL;
}

void* thread2_func(void* arg) {
    a = atomic_load(&y);
    atomic_store(&x, 3);
    b = atomic_load(&x);
    return NULL;
}

int main() {
    pthread_t thread1, thread2;

    if (pthread_create(&thread1, NULL, &thread1_func, NULL)) {
        fprintf(stderr, "Error creating thread 1\n");
        return 1;
    }

    if (pthread_create(&thread2, NULL, &thread2_func, NULL)) {
        fprintf(stderr, "Error creating thread 2\n");
        return 1;
    }

    if (pthread_join(thread1, NULL)) {
        fprintf(stderr, "Error joining thread 1\n");
        return 2;
    }

    if (pthread_join(thread2, NULL)) {
        fprintf(stderr, "Error joining thread 2\n");
        return 2;
    }

    printf("Thread 1 executed: x := 1; y := 1; x := 2;\n");
    printf("Thread 2 executed: a = y; x = 3; b = x;\n");
    printf("Values after execution: a = %d, b = %d\n", a, b);

    return 0;
}

