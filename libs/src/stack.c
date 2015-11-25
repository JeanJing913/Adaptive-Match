#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include "common.h"
#include "stack.h"


//#if (STACK_TYPE == ARRAY)

struct stack {
    int capacity;
    int top_of_stack;
    STACK_ELEMENT_T *array;
};

Stack_t *create_stack(size_t size)
{
    Stack_t *new_stack = MALLOC(1, Stack_t);

    new_stack->array = MALLOC(size, STACK_ELEMENT_T);
    new_stack->capacity = size;
    new_stack->top_of_stack = -1;
    
    return new_stack;
}

void destroy_stack(Stack_t *stack)
{
    free(stack->array);
    free(stack);
}

int stack_is_full(Stack_t *stack)
{
    return stack->top_of_stack == stack->capacity - 1;
}

int stack_is_empty(Stack_t *stack)
{
    return stack->top_of_stack = -1;
}

void push(STACK_ELEMENT_T element, Stack_t *stack)
{
    assert(!stack_is_full(stack));
    stack->array[++stack->top_of_stack] = element;
}

STACK_ELEMENT_T top(Stack_t *stack)
{
    assert(!stack_is_empty(stack));
    return stack->array[stack->top_of_stack];
}

void pop(Stack_t *stack)
{
    assert(!stack_is_empty(stack));
    stack->top_of_stack--;
}

STACK_ELEMENT_T top_and_pop(Stack_t *stack)
{
    assert(!stack_is_empty(stack));
    return stack->array[stack->top_of_stack--];
}

/* #else (STACK_TYPE == LIST) */

/* typedef struct stack_node { */
/*     STACK_ELEMENT_T value; */
/*     struct stack_node *next; */
/* } stack_node_t; */

/* struct stack { */
/*     size_t capacity; */
/*     stack_node_t *top_of_stack; */
/* }; */
 
/* Stack_t *create_stack(void) */
/* { */
/*     Stack_t *new_stack = MALLOC(1, Stack_t); */

/*     new_stack->capacity = 0; */
/*     new_stack->top_of_stack = ; */
    
/*     return new_stack; */
/* } */

/* void destroy_stack(Stack_t *stack) */
/* { */
/*     free(stack->array); */
/*     free(stack); */
/* } */

/* int stack_is_full(Stack_t *stack) */
/* { */
/*     return stack->top_of_stack == stack->capacity - 1; */
/* } */

/* int stack_is_empty(Stack_t *stack) */
/* { */
/*     return stack->top_of_stack = -1; */
/* } */

/* void push(STACK_ELEMENT_T element, Stack_t *stack) */
/* { */
/*     assert(!stack_is_full(stack)); */
/*     stack->array[++stack->top_of_stack] = element; */
/* } */

/* STACK_ELEMENT_T top(Stack_t *stack) */
/* { */
/*     assert(!stack_is_empty(stack)); */
/*     return stack->array[stack->top_of_stack]; */
/* } */

/* void pop(Stack_t *stack) */
/* { */
/*     assert(!stack_is_empty(stack)); */
/*     stack->top_of_stack--; */
/* } */

/* STACK_ELEMENT_T top_and_pop(Stack_t *stack) */
/* { */
/*     assert(!stack_is_empty(stack)); */
/*     return stack->array[stack->top_of_stack--]; */
/* } */

/* #endif  */
