#include <iostream>
#include <thread>
#include <atomic>

std::atomic<int> x = ATOMIC_VAR_INIT(0);
std::atomic<int> y = ATOMIC_VAR_INIT(0);

void thread1_func() {
    // Thread 1: Write operations
    x.store(1, std::memory_order_release);
    y.store(1, std::memory_order_release);
    x.store(2, std::memory_order_release);
}

void thread2_func() {
    int local_y;
    int local_x;

    // Thread 2: Read and Write operations
    local_y = y.load(std::memory_order_acquire);
    x.store(3, std::memory_order_release);
    local_x = x.load(std::memory_order_acquire);
    y.store(2, std::memory_order_release);

    // Output the values read by Thread 2
    std::cout << "Thread 2: y = " << local_y << ", x = " << local_x << std::endl;
}

void thread3_func() {
    int local_x;
    int local_y;

    // Thread 3: Read operations
    local_x = x.load(std::memory_order_acquire);
    local_y = y.load(std::memory_order_acquire);

    // Output the values read by Thread 3
    std::cout << "Thread 3: x = " << local_x << ", y = " << local_y << std::endl;
}

int main() {
    // Create threads
    std::thread t1(thread1_func);
    std::thread t2(thread2_func);
    std::thread t3(thread3_func);

    // Join threads
    t1.join();
    t2.join();
    t3.join();

    return 0;
}

