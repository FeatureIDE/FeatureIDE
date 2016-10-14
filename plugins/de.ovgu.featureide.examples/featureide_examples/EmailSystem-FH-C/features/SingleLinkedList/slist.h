typedef struct node_s
{
  void *data;
  struct node_s *next;
} NODE;


NODE *list_create (void *data);

NODE *list_insert_after (NODE * node, void *data);

NODE *list_insert_beginning (NODE * list, void *data);

int list_remove (NODE * list, NODE * node);

int list_foreach (NODE * node, int (*func) (void *));

NODE *list_find (NODE * node, int (*func) (void *, void *), void *data);
