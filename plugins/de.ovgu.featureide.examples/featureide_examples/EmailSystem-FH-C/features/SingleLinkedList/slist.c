/* Copyright (c) 2009 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Singly_linked_list_(C)?action=history&offset=20081126164854

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Retrieved from: http://en.literateprograms.org/Singly_linked_list_(C)?oldid=15494
*/

#include "slist.h"
#include<stdlib.h>
#include<stdio.h>

NODE *
list_create (void *data)
{
  NODE *node;
  if (!(node = malloc (sizeof (NODE))))
    return NULL;
  node->data = data;
  node->next = NULL;
  return node;
}

NODE *
list_insert_after (NODE * node, void *data)
{
  NODE *newnode;
  newnode = list_create (data);
  newnode->next = node->next;
  node->next = newnode;
  return newnode;
}

NODE *
list_insert_beginning (NODE * list, void *data)
{
  NODE *newnode;
  newnode = list_create (data);
  newnode->next = list;
  return newnode;
}

int
list_remove (NODE * list, NODE * node)
{
  while (list->next && list->next != node)
    list = list->next;
  if (list->next)
    {
      list->next = node->next;
      free (node);
      return 0;
    }
  else
    return -1;
}

int
list_foreach (NODE * node, int (*func) (void *))
{
  while (node)
    {
      if (func (node->data) != 0)
	return -1;
      node = node->next;
    }
  return 0;
}

NODE *
list_find (NODE * node, int (*func) (void *, void *), void *data)
{
  while (node)
    {
      if (func (node->data, data) > 0)
	return node;
      node = node->next;
    }
  return NULL;
}
