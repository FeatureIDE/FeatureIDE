#include "Client.h"

void
addMessageID (struct client *client, struct email *msg)
{
  if (!msg->id)
    {
      /*
         msg->id = (char *) malloc (sizeof (int) + strlen (client->name));
         sprintf (msg->id, "%s%i", client->name, client->idCounter);
       */
      msg->id = client->idCounter;
      client->idCounter++;
    }
}


void
outgoing (struct client *client, struct email *msg)
{
  addMessageID (client, msg);
  original (client, msg);
}
