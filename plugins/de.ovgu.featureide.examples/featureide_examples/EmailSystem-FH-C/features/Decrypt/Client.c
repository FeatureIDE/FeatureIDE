#include <string.h>
#include "Client.h"
// removes the decryption flag if possible
void
decrypt (struct client *client, struct email *msg)
{
// VERIFICATION HOOK
  int verificationHook_isKeyPairValid =
    isKeyPairValid (msg->encryptionKey, client->privateKey);
// printf ("\n> hook\n%i\n\n", verificationHook_isKeyPairValid);
// VERIFICATION HOOK END
  if (!client->privateKey)
    return;
  if (msg->isEncrypted == 1
      && 0 == strcmp (msg->encryptionKey, client->privateKey))
    {
      msg->encryptionKey = NULL;
      msg->isEncrypted = 0;
    }
}

void
incoming (struct client *client, struct email *msg)
{
// VERIFICATION HOOK
  int verificationHook_isEncrypted = isEncrypted (msg);
  printf ("incoming:\nisEncrypted = %i\nid = %i\n",
	  verificationHook_isEncrypted, msg->id);
// VERIFICATION HOOK END
  decrypt (client, msg);
  original (client, msg);
}
