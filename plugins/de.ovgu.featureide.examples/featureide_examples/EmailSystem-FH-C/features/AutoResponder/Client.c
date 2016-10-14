#include <string.h>
#include "Client.h"
void
autoRespond (struct client *client, struct email *msg)
{
  if (!client->autoResponse || !isReadable (msg))
    return;
  struct email *response = cloneEmail (msg);
  response->to = strdup (msg->from);
  response->body = strdup (client->autoResponse);
  char *respondPrefix = "Auto-Response ";
  response->subject =
    (char *) malloc (strlen (respondPrefix) + strlen (msg->subject));
  strcat (response->subject, respondPrefix);
  strcat (response->subject, msg->subject);
  outgoing (client, response);
}

void
incoming (struct client *client, struct email *msg)
{
  autoRespond (client, msg);
  original (client, msg);
}
