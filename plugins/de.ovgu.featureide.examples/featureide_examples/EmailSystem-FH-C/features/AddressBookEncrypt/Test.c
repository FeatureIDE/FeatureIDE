#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include "Client.h"
//#include "Email.h"

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
  struct addressBookEntry *addressBookEntry =
    (struct addressBookEntry *) malloc (sizeof (struct addressBookEntry));
  addressBookEntry->alias = "someAlias";
  addressBookEntry->address = list_create ("rjh");
  addressBookEntry->address =
    list_insert_beginning (addressBookEntry->address, "chucknorris");
  addressBookEntry->address =
    list_insert_beginning (addressBookEntry->address, "mcguyver");
  NODE *addressBook = list_create (addressBookEntry);
  bob->addressBook = addressBook;

  struct email *mail = (struct email *) malloc (sizeof (struct email));
  mail->to = "someAlias";
  mail->subject = "<some subject>";
  mail->body = "<some body>";

  outgoing (bob, mail);

  return 0;
}
