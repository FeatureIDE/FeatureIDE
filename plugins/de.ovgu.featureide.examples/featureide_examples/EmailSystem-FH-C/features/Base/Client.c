#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "Client.h"

// outgoing emails leave the client at this point. here they are put in an outgoing queue instead.
void
mail (struct client *client, struct email *msg)
{
  //TODO 
//  printf ("=> %s MAIL\n", client->name);
//  printMail (msg);
  if (!client->outgoingBuffer)
    client->outgoingBuffer = list_create (msg);
  else
    list_insert_after (client->outgoingBuffer, msg);
}

// emails to be sent are processed by this method before beeing mailed.
void
outgoing (struct client *client, struct email *msg)
{
  msg->from = strdup (client->name);
  mail (client, msg);
}

// incoming emails reach the user at this point. here they are put in a mailbox.
void
deliver (struct client *client, struct email *msg)
{
  //TODO
  // printf ("=> %s DELIVER\n", client->name);
  //printMail (msg);
}

// incoming emails are processed by this method before delivery.
void
incoming (struct client *client, struct email *msg)
{
  deliver (client, msg);
}
