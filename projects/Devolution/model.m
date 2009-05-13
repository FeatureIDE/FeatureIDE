Devolution : [Addressbook] [Mail] [Messaging] [Kalender] [RSS] [ToDo] Base :: _Devolution ;

Mail : Protokolle [AntiSpam] MailBase :: _Mail ;

Protokolle : Verschicken Empfangen+ :: _Protokolle ;

Verschicken : SMTP [AB_SMTP_Interact] :: _Verschicken ;

Empfangen : IMAP
	| POP3 ;

Messaging : Dienste+ [Upload] [AB_IM_Interact] :: _Messaging ;

Dienste : IRC
	| IMViews IMProtokolle+ InstantBase :: Instant ;

IMViews : IMTextView
	| IMXMLView ;

IMProtokolle : Jabber ;

Kalender : Synchronisation* :: _Kalender ;

Synchronisation : iCal
	| CalDAV
	| GoogleCalendar ;

