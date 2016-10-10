struct email
{
  int id;
  char *from;
  char *to;
  char *subject;
  char *body;
};

struct email *cloneEmail (struct email *msg);

void printMail (struct email *msg);

int isReadable (struct email *msg);
