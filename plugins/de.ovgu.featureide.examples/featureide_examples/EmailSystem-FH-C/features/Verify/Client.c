// checks for a valid signature and replaces it by a flag signaling a verified signature
void
verify (struct client *client, struct email *msg)
{
  // VERIFICATION HOOK
  int verificationHook_list_find =
    list_find (client->userPublicKeyPairs, findUserPublicKeyPair,
	       msg->from) != NULL;
  printf ("\n> hook\n%i\n\n", verificationHook_list_find);
  // VERIFICATION HOOK END
  // VERIFICATION HOOK
  if (verificationHook_list_find)
    {
      int verificationHook_isKeyPairValid =
	isKeyPairValid (((struct userPublicKeyPair
			  *) (list_find (client->userPublicKeyPairs,
					 findUserPublicKeyPair,
					 msg->from)->data))->publicKey,
			msg->signKey);
      printf ("\n> hook\n%i\n\n", verificationHook_isKeyPairValid);
    }
  // VERIFICATION HOOK END
  // VERIFICATION HOOK
  int verificationHook_isReadable = isReadable (msg);
  // VERIFICATION HOOK END
  if (!isReadable (msg) || !msg->isSigned)
    return;
  NODE *foundPublicKeyPair =
    list_find (client->userPublicKeyPairs, findUserPublicKeyPair, msg->from);
  if (foundPublicKeyPair
      && 0 == strcmp (msg->signKey,
		      ((struct userPublicKeyPair *)
		       foundPublicKeyPair->data)->publicKey))
    {
      msg->isSignatureVerified = 1;
    }
}

void
incoming (struct client *client, struct email *msg)
{
  verify (client, msg);
  original (client, msg);
}

void
mail (struct client *client, struct email *msg)
{
// VERIFICATION HOOK
  int verificationHook_isVerified = isVerified (msg);
// VERIFICATION HOOK END
  original (client, msg);
}
