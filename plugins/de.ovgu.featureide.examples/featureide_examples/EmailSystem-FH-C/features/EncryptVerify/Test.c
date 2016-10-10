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
  struct userPublicKeyPair *userPublicKeyPairBob =
    (struct userPublicKeyPair *) malloc (sizeof (struct userPublicKeyPair));
  userPublicKeyPairBob->user = "bob";
  userPublicKeyPairBob->publicKey = "key-bob";
  NODE *userPublicKeyPairsRjh = list_create (userPublicKeyPairBob);
  rjh->userPublicKeyPairs = userPublicKeyPairsRjh;

  // rjh has lost his private key thus he cannot decrypt messages
  rjh->privateKey = NULL;

  struct email *mail = (struct email *) malloc (sizeof (struct email));
  mail->to = "rjh";
  mail->subject = "<some subject>";
  mail->body = "<some body>";

  outgoing (bob, mail);
  // rjh cannot verify the message since decryption fails
  incoming (rjh, mail);

  return 0;
}
