#include "slist.h"

struct client
{
  NODE *addressBook;
};

struct addressBookEntry
{
  char *alias;
  NODE *address;
};

// TODO remove after fixing the composition-function-order-problem
void resolveAlias (struct client *client, struct email *msg);
