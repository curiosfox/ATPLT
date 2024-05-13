#include <stdatomic.h>
#include <pthread.h>
#include <stdio.h>

atomic_int x = ATOMIC_VAR_INIT(0);
atomic_int y = ATOMIC_VAR_INIT(0);
int a = 0;
int b = 0;

void* thread1_func(void* arg) {
    atomic_store_explicit(&x, 5, memory_order_release);
    return NULL;
}

void* thread2_func(void* arg) {
    atomic_store_explicit(&y, 6, memory_order_release);
    return NULL;
}

void* thread3_func(void* arg) {
    a = atomic_load_explicit(&x, memory_order_acquire);
    b = atomic_load_explicit(&y, memory_order_acquire);
    return NULL;
}

int main() {
    pthread_t thread1, thread2, thread3;
    pthread_create(&thread1, NULL, &thread1_func, NULL);
    pthread_create(&thread2, NULL, &thread2_func, NULL);
    pthread_create(&thread3, NULL, &thread3_func, NULL);
    pthread_join(thread1, NULL);
    pthread_join(thread2, NULL);
    pthread_join(thread3, NULL);
    printf("Values after execution: a = %d, b = %d\n", a, b);
    return 0;
}

