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
  rjh->forwardReceiver = "chucknorris";

  struct client *chucknorris =
    (struct client *) malloc (sizeof (struct client));
  chucknorris->name = "chucknorris";
  struct userPublicKeyPair *userPublicKeyPairBob =
    (struct userPublicKeyPair *) malloc (sizeof (struct userPublicKeyPair));
  userPublicKeyPairBob->user = "bob";
  userPublicKeyPairBob->publicKey = "key-bob";
  NODE *userPublicKeyPairsChucknorris = list_create (userPublicKeyPairBob);
  chucknorris->userPublicKeyPairs = userPublicKeyPairsChucknorris;

  struct email *mail = (struct email *) malloc (sizeof (struct email));
  mail->to = "rjh";
  mail->subject = "<some subject>";
  mail->body = "<some body>";

  outgoing (bob, mail);
  incoming (rjh, mail);
  // chucknorris receives a forwarded message by rjh but doesn't verify the signature of the originator bob though chucknorris has a valid public key of bob.
  incoming (chucknorris, (struct email *) rjh->outgoingBuffer->data);

  return 0;
}
