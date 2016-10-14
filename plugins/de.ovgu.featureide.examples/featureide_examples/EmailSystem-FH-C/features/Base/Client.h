#include "Email.h"
#include "slist.h"

/*
 * two sorts of emails are processed by this client: incoming and outgoing ones.
 * control flow is
 * email from internet > incoming > deliver > receipient receives mail
 * sender writes email > outgoing > mail > email sent through internet
 */
struct client
{
  char *name;
  NODE *outgoingBuffer;
};

void outgoing (struct client *client, struct email *msg);

void incoming (struct client *client, struct email *msg);
