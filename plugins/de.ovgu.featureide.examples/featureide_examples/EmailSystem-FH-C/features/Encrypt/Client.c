void
encrypt (struct client *client, struct email *msg)
{
  NODE *foundPublicKeyPair =
    list_find (client->userPublicKeyPairs, findUserPublicKeyPair, msg->to);
  if (foundPublicKeyPair)
    {
      msg->encryptionKey =
	strdup (((struct userPublicKeyPair *) foundPublicKeyPair->data)->
		publicKey);
      msg->isEncrypted = 1;
    }
}

void
outgoing (struct client *client, struct email *msg)
{
  encrypt (client, msg);
  original (client, msg);
}

void
incoming (struct client *client, struct email *msg)
{
  original (client, msg);
}


void
mail (struct client *client, struct email *msg)
{
// VERIFICATION HOOK
  int verificationHook_isEncrypted = isEncrypted (msg);
  printf ("mail:\nisEncrypted = %i\nid = %i\n", verificationHook_isEncrypted,
	  msg->id);
// VERIFICATION HOOK END
  original (client, msg);
}
