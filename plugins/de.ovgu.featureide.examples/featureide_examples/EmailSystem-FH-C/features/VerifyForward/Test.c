#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "Client.h"

int
main (void)
{
  struct client *bob = (struct client *) malloc (sizeof (struct client));
  bob->name = "bob";
  bob->privateKey = "key-bob";

  struct client *rjh = (struct client *) malloc (sizeof (struct client));
  rjh->name = "rjh";
  // rjh has no private key, thus he cannot sign messages
  rjh->forwardReceiver = "chucknorris";
  struct userPublicKeyPair *userPublicKeyPairBob =
    (struct userPublicKeyPair *) malloc (sizeof (struct userPublicKeyPair));
  userPublicKeyPairBob->user = "bob";
  userPublicKeyPairBob->publicKey = "key-bob";
  NODE *userPublicKeyPairsRjh = list_create (userPublicKeyPairBob);
  rjh->userPublicKeyPairs = userPublicKeyPairsRjh;

  struct email *mail = (struct email *) malloc (sizeof (struct email));
  mail->to = "rjh";
  mail->subject = "<some subject>";
  mail->body = "<some body>";

  outgoing (bob, mail);
  incoming (rjh, mail);

  return 0;
}
