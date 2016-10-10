#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "Client.h"

int
main (void)
{
  struct client *bob = (struct client *) malloc (sizeof (struct client));
  bob->name = "bob";
  bob->privateKey = "key-bob";
  struct userPublicKeyPair *userPublicKeyPairRjh =
    (struct userPublicKeyPair *) malloc (sizeof (struct userPublicKeyPair));
  userPublicKeyPairRjh->user = "rjh";
  userPublicKeyPairRjh->publicKey = "key-rjh";
  NODE *userPublicKeyPairsBob = list_create (userPublicKeyPairRjh);
  bob->userPublicKeyPairs = userPublicKeyPairsBob;

  struct client *rjh = (struct client *) malloc (sizeof (struct client));
  rjh->name = "rjh";
  rjh->privateKey = "key-rjh";

  // rjh changes his private key, rjh doesn't receive the updated public key (i.e. he actually has no valid public key from bob). Thus rjh cannot decrypt bob's message
  rjh->privateKey = "key-rjh-new";

  struct email *mail = (struct email *) malloc (sizeof (struct email));
  mail->to = "rjh";
  mail->subject = "<some subject>";
  mail->body = "<some body>";

  outgoing (bob, mail);
  incoming (rjh, mail);

  return 0;
}
