#include "Client.h"
#include <string.h>

void
forward (struct client *client, struct email *msg)
{
  // VERIFICATION HOOK
  int verificationHook_isReadable = isReadable (msg);
  // VERIFICATION HOOK END
  if (!client->forwardReceiver || !isReadable (msg))
    return;
  struct email *clone = cloneEmail (msg);
  clone->to = strdup (client->forwardReceiver);
  outgoing (client, clone);
}

void
incoming (struct client *client, struct email *msg)
{
  forward (client, msg);
  original (client, msg);
}
