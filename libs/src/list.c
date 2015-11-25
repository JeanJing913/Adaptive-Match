#include <stdio.h>
#include <stdlib.h>


#define SPACE_SIZE 1000


typedef char * Value_t ;

typedef struct list_node {
    Value_t  value;
    struct list_node *next;
}List_Node_t;

List_Node_t list_space[SPACE_SIZE];
List_Node_t *first_free;

void list_space_ini(void)
{
    List_Node_t *p;
    first_free = list_space;

    for (p = list_space; p < list_space + SPACE_SIZE - 1; p++)
        p->next = p + 1;

    p->next = NULL;
}

List_Node_t *list_space_malloc(void)
{
    List_Node_t *tmp;

    if (first_free == NULL) {
        fprintf(stderr, "List space overflow!\n");
        exit(EXIT_FAILURE);
    } else {
        tmp = first_free;
        first_free = first_free->next;
    }

    return tmp;
}

void list_space_free(List_Node_t *node)
{
    node->next = first_free;
    first_free = node;
}
/*
int main(int argc, char **argv)
{
    List_Node_t *list_1, *list_2;

    list_space_ini();
}*/

