/* This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */

/* Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
*/

#include "threads/synch.h"
#include <stdio.h>
#include <string.h>
#include "threads/interrupt.h"
#include "threads/thread.h"

/* Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
     decrement it.

   - up or "V": increment the value (and wake up one waiting
     thread, if any). */
void
sema_init (struct semaphore *sema, unsigned value) 
{
  ASSERT (sema != NULL);

  sema->value = value;
  list_init (&sema->waiters);
}

/* Down or "P" operation on a semaphore.  Waits for SEMA's value
   to become positive and then atomically decrements it.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but if it sleeps then the next scheduled
   thread will probably turn interrupts back on. */
void
sema_down (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);
  ASSERT (!intr_context ());
  
  old_level = intr_disable ();
  while (sema->value == 0) 
    {
      list_push_back (&sema->waiters, &thread_current ()->elem);
      thread_block ();
    }
  sema->value--;
  intr_set_level (old_level);
}

/* Down or "P" operation on a semaphore, but only if the
   semaphore is not already 0.  Returns true if the semaphore is
   decremented, false otherwise.

   This function may be called from an interrupt handler. */
bool
sema_try_down (struct semaphore *sema) 
{
  enum intr_level old_level;
  bool success;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (sema->value > 0) 
    {
      sema->value--;
      success = true; 
    }
  else
    success = false;
  intr_set_level (old_level);

  return success;
}

/* Up or "V" operation on a semaphore.  Increments SEMA's value
   and wakes up one thread of those waiting for SEMA, if any.

   This function may be called from an interrupt handler. */
void
sema_up (struct semaphore *sema) 
{
  enum intr_level old_level;

  ASSERT (sema != NULL);

  old_level = intr_disable ();
  if (!list_empty (&sema->waiters))
  { 
    struct list_elem *e = list_max(&sema->waiters, thread_lower_priority, NULL);    
    struct thread *t = list_entry (e, struct thread, elem);
    list_remove(e);
    thread_unblock (t);
  }
  sema->value++;
  thread_yield_to_higher_priority();
  intr_set_level (old_level);
}

static void sema_test_helper (void *sema_);

/* Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */
void
sema_self_test (void) 
{
  struct semaphore sema[2];
  int i;

  printf ("Testing semaphores...");
  sema_init (&sema[0], 0);
  sema_init (&sema[1], 0);
  thread_create ("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
  for (i = 0; i < 10; i++) 
    {
      sema_up (&sema[0]);
      sema_down (&sema[1]);
    }
  printf ("done.\n");
}

/* Thread function used by sema_self_test(). */
static void
sema_test_helper (void *sema_) 
{
  struct semaphore *sema = sema_;
  int i;

  for (i = 0; i < 10; i++) 
    {
      sema_down (&sema[0]);
      sema_up (&sema[1]);
    }
}

/* Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */
void
lock_init (struct lock *lock)
{
  int i = 0;
  ASSERT (lock != NULL);

  lock->holder = NULL;
  for(; i < PRIORITY_DONATION_DEPTH; i++)
  {
    lock->threadsWaiting[i] = NULL;
  }
  sema_init (&lock->semaphore, 1);
}

/* Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
lock_acquire (struct lock *lock)
{
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (!lock_held_by_current_thread (lock));
  int i = 0;
  struct thread * curThread = thread_current();

  if(lock->holder != NULL)
  {
    //Another thread is waiting on a lock. Register it in the list of threads waiting on this lock.
    for(; i < PRIORITY_DONATION_DEPTH; i++)
    {
      if(lock->threadsWaiting[i] != NULL)
      {
        lock->threadsWaiting[i] = curThread;
        break;
      }
    }

    //The priority of the thread holding the lock should always be set equal to the highest priority thread that is waiting on it.
    if(curThread->priority > lock->holder->priority)
    {
      lock->holder->priority = curThread->priority;
    }
  }
  
  sema_down (&lock->semaphore);
  //add_lock_to_thread(lock, curThread);
  for( i = 0; i < PRIORITY_DONATION_DEPTH; i++)
  {
    if(curThread->locks_held[i] == NULL)
    {
       curThread->locks_held[i] = lock;
       break;
    }
  }
  lock->holder = curThread;
}

/* Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */
bool
lock_try_acquire (struct lock *lock)
{
  bool success;

  ASSERT (lock != NULL);
  ASSERT (!lock_held_by_current_thread (lock));

  success = sema_try_down (&lock->semaphore);
  if (success)
    lock->holder = thread_current ();
  return success;
}

/* Releases LOCK, which must be owned by the current thread.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */
void lock_release (struct lock *lock) 
{
  int i;
  ASSERT (lock != NULL);
  ASSERT (lock_held_by_current_thread (lock));
  struct thread * curThread = thread_current();

  //Checks if curThread was still in the waitlist for the lock and removes it if it was.
  for(i = 0; i < PRIORITY_DONATION_DEPTH; i++)
  {
    if(lock->threadsWaiting[i] == curThread)
    {
      lock->threadsWaiting[i] = NULL;
    }
  }

  //removes the lock from the current thread.
  //remove_lock_from_thread(lock, curThread);
  for( i = 0; i < PRIORITY_DONATION_DEPTH; i++)
  {
    if(thread_current()->locks_held[i] == lock)
       thread_current()->locks_held[i] = NULL;
  }

  lock->holder = NULL;
  //Check to see if this thread got a donated priority, if yes then reset our priority
  if(thread_current()->priority != thread_current()->original_priority)
  {
    thread_current()->priority = find_priority_for_thread(thread_current());
  }
  sema_up (&lock->semaphore);
}

/*Function to find the next priority based on the lock.*/

int find_priority_for_thread(struct thread * thread)
{
  ASSERT (thread != NULL);
  int i, j;
  int maxPriority = -1;

  //Check to see if this thread got a donated priority, if yes then reset our priority
  //if(thread->priority != thread->original_priority)
  //{
    for( i = 0; i < PRIORITY_DONATION_DEPTH; i++)
    {
      for( j = 0; j < PRIORITY_DONATION_DEPTH; j++)
      {
        if((thread->locks_held[i] != NULL) && (thread->locks_held[i]->threadsWaiting[j] != NULL) && ((thread->locks_held[i]->threadsWaiting[j]->priority) > maxPriority))
          maxPriority = thread->locks_held[i]->threadsWaiting[j]->priority;
      }
    }
    
    return maxPriority;
  //}

  return thread->original_priority;
}

/*Adds the lock provided to the thread provided.*/
void add_lock_to_thread(struct lock * lock, struct thread * thread)
{
  ASSERT(lock != NULL);
  ASSERT(thread != NULL);

  int i;
  for( i = 0; i < PRIORITY_DONATION_DEPTH; i++)
  {
    if(thread->locks_held[i] == NULL)
    {
       thread->locks_held[i] = lock;
       break;
    }
  }
}

/*Removes the lock provided from the thread provided.*/
void remove_lock_from_thread(struct lock * lock, struct thread * thread)
{
  ASSERT(lock != NULL);
  ASSERT(thread != NULL);

  int i;
  for( i = 0; i < PRIORITY_DONATION_DEPTH; i++)
  {
    if(thread->locks_held[i] == lock)
       thread->locks_held[i] = NULL;
  }
}

/* Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */
bool
lock_held_by_current_thread (const struct lock *lock) 
{
  ASSERT (lock != NULL);

  return lock->holder == thread_current ();
}

/* One semaphore in a list. */
struct semaphore_elem 
  {
    struct list_elem elem;              /* List element. */
    struct semaphore semaphore;         /* This semaphore. */
    int sema_priority;
  };

/* Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */
/*bool cond_lower_priority(const struct list_elem *a_, const struct list_elem *b_, void *aux UNUSED)
{
  return (&list_entry(a_, struct thread_elem, elem)->priority) < (&list_entry(b_, struct thread_elem, elem)-> priority);
}*/

void
cond_init (struct condition *cond)
{
  ASSERT (cond != NULL);

  list_init (&cond->waiters);
}

bool
cond_priority(const struct list_elem *ae, const struct list_elem *be, void *aux UNUSED)
{
  struct semaphore_elem *l, *r;
  l = list_entry(ae, struct semaphore_elem, elem);
  r = list_entry(be, struct semaphore_elem, elem);
  return (l->sema_priority > r->sema_priority);

}

/* Atomically releases LOCK and waits for COND to be signaled by
   some other piece of code.  After COND is signaled, LOCK is
   reacquired before returning.  LOCK must be held before calling
   this function.

   The monitor implemented by this function is "Mesa" style, not
   "Hoare" style, that is, sending and receiving a signal are not
   an atomic operation.  Thus, typically the caller must recheck
   the condition after the wait completes and, if necessary, wait
   again.

   A given condition variable is associated with only a single
   lock, but one lock may be associated with any number of
   condition variables.  That is, there is a one-to-many mapping
   from locks to condition variables.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
cond_wait (struct condition *cond, struct lock *lock) 
{
  struct semaphore_elem waiter;

  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));
  
  sema_init (&waiter.semaphore, 0);
  waiter.sema_priority = thread_current()->priority;
  list_insert_ordered(&cond->waiters, &waiter.elem, cond_priority, NULL);
  //list_push_back (&cond->waiters, &waiter.elem);
  lock_release (lock);
  sema_down (&waiter.semaphore);
  lock_acquire (lock);
}

/* If any threads are waiting on COND (protected by LOCK), then
   this function signals one of them to wake up from its wait.
   LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */

void
cond_signal (struct condition *cond, struct lock *lock UNUSED) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);
  ASSERT (!intr_context ());
  ASSERT (lock_held_by_current_thread (lock));
  //enum intr_level old_level;
  if (!list_empty (&cond->waiters)) 
  {
    //need to find the max priority semaphore elem, call sema up on it
    //struct list_elem *e ;
    /*struct list_elem *e = list_begin(&cond->waiters);
    struct list_elem *max_elem = e;
    struct thread *t = NULL;
    struct thread *max_p = list_entry(e, struct thread, &waiters.elem);
    int x = max_p->priority;
    for (; e != list_end(&cond->waiters); e = list_next(e))
    {
      t = list_entry(e, struct thread, &waiters.elem);
      if(&t->priority > &max_p->priority)
      {
        max_p = t;
        max_elem = e;
      }
    
    }*/
    //sema_up (&list_entry (max_elem, struct semaphore_elem, elem)->semaphore);
    //struct thread *t = list_entry (list_max(&cond->waiters, cond_lower_priority, NULL), struct thread, elem);
    //sema_up (&list_entry (list_max(&cond->waiters, cond_lower_priority, NULL), struct semaphore_elem, elem)->semaphore);
    sema_up (&list_entry (list_pop_front (&cond->waiters), struct semaphore_elem, elem)->semaphore);
  }
}

/* Wakes up all threads, if any, waiting on COND (protected by
   LOCK).  LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_broadcast (struct condition *cond, struct lock *lock) 
{
  ASSERT (cond != NULL);
  ASSERT (lock != NULL);

  while (!list_empty (&cond->waiters))
    cond_signal (cond, lock);
}


