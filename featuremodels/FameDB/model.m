DB : OS BufferMgr [DebugLogging] Storage :: _DB ;

OS : NutOS
	| Win ;

BufferMgr : MemAlloc PageRepl :: Persistent
	| InMemory ;

MemAlloc : Static
	| Dynamic ;

PageRepl : LRU
	| LFU ;

Storage : API+ Index :: _Storage ;

API : get
	| put
	| delete ;

Index : BTree
	| Unindexed ;

