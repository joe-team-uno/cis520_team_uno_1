#ifndef THREADS_SYNCH_H
#define THREADS_SYNCH_H

#include <list.h>
#include <stdbool.h>

//used in threads and sync
#define PRIORITY_DONATION_DEPTH 8 

/* A counting semaphore. */
struct semaphore 
  {
    unsigned value;             /* Current value. */
    struct list waiters;        /* List of waiting threads. */
  };

void sema_init (struct semaphore *, unsigned value);
void sema_down (struct semaphore *);
bool sema_try_down (struct semaphore *);
void sema_up (struct semaphore *);
void sema_self_test (void);

/* Lock. */
struct lock 
  {
    struct thread *holder;           /* Thread holding lock (for debugging). */
    struct thread *threadsWaiting[PRIORITY_DONATION_DEPTH]; /* A list of threads that need access to the locked resource. Used to calculate donated priorities */
    struct semaphore semaphore;      /* Binary semaphore controlling access. */
  };

void lock_init (struct lock *);
void lock_acquire (struct lock *);
bool lock_try_acquire (struct lock *);
void lock_release (struct lock *);
bool lock_held_by_current_thread (const struct lock *);
int find_priority_for_thread(struct thread * thread);
void add_lock_to_thread(struct lock * lock, struct thread * thread);
void remove_lock_from_thread(struct lock * lock, struct thread * thread);

/* Condition variable. */
struct condition 
  {
    struct list waiters;        /* List of waiting threads. */
  };


void cond_init (struct condition *);
void cond_wait (struct condition *, struct lock *);
void cond_signal (struct condition *, struct lock *);
void cond_broadcast (struct condition *, struct lock *);
bool cond_priority(const struct list_elem *ae, const struct list_elem *be, void *);

/* Optimization barrier.

   The compiler will not reorder operations across an
   optimization barrier.  See "Optimization Barriers" in the
   reference guide for more information.*/
#define barrier() asm volatile ("" : : : "memory")

#endif /* threads/synch.h */
