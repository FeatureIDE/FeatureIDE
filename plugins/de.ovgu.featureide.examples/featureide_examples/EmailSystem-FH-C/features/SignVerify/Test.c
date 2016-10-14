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

  struct client *rjh = (struct client *) malloc (sizeof (struct client));
  rjh->name = "rjh";
  rjh->privateKey = "key-rjh";
  struct userPublicKeyPair *userPublicKeyPairBob =
    (struct userPublicKeyPair *) malloc (sizeof (struct userPublicKeyPair));
  userPublicKeyPairBob->user = "bob";
  userPublicKeyPairBob->publicKey = "key-bob";
  NODE *userPublicKeyPairsRjh = list_create (userPublicKeyPairBob);
  rjh->userPublicKeyPairs = userPublicKeyPairsRjh;

  // bob has changed his private key, rjh didn't receive the updated public key (i.e. he actually has no valid public key from bob). Thus rjh cannot verify bobs signed message
  bob->privateKey = "key-bob-new";

  struct email *mail = (struct email *) malloc (sizeof (struct email));
  mail->to = "rjh";
  mail->subject = "<some subject>";
  mail->body = "<some body>";

  outgoing (bob, mail);
  incoming (rjh, mail);

  return 0;
}
