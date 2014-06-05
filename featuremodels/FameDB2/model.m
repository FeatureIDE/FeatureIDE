DB : OS BufferMgr [DebugLogging] Storage :: _DB ;

OS : NutOS
	| Win ;

BufferMgr : MemAlloc PageRepl :: Persistent
	| InMemory ;

MemAlloc : Static
	| Dynamic ;

PageRepl : LRU
	| LFU ;

Storage : API+ [BTree] [Unindexed] :: _Storage ;

API : get
	| put
	| delete ;

%%

(not Storage or BTree or Unindexed) and (not BTree or not Unindexed) ;

