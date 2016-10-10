int
findAddressBookEntry (void *listdata, void *searchdata)
{
  return strcmp
    (((struct addressBookEntry *) listdata)->alias,
     (char *) searchdata) ? 0 : 1;
}

void
resolveAlias (struct client *client, struct email *msg)
{
  if (!client->addressBook)
    return;
  struct email *clone = cloneEmail (msg);
  NODE *found =
    list_find (client->addressBook, findAddressBookEntry, clone->to);
  if (!found)
    return;
  NODE *address = ((struct addressBookEntry *) found->data)->address;
  if (address)
    {
      msg->to = strdup (address->data);
      address = address->next;
    }
  while (address)
    {
      struct email *newmsg = cloneEmail (clone);
      newmsg->to = strdup (address->data);
      address = address->next;
      outgoing (client, newmsg);
    }
}

void
outgoing (struct client *client, struct email *msg)
{
  resolveAlias (client, msg);
  original (client, msg);
}
