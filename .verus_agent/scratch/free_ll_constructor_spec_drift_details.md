## LL::empty has=True impacted=[] new=False removed=False
signature modified before= pub fn empty () -> (ll: LL) after= pub fn empty () -> LL
## LL::new has=True impacted=[] new=False removed=False
signature modified before= pub fn new (Ghost(page_id): Ghost<PageId>, Ghost(fixed_page): Ghost<bool>, Ghost(instance): Ghost<Mim::Instance>, Ghost(block_size): Ghost<nat>, Ghost(heap_id): Ghost<Option<HeapId>>, ) -> (ll: LL) after= pub fn new (Ghost(page_id): Ghost<PageId>, Ghost(fixed_page): Ghost<bool>, Ghost(instance): Ghost<Mim::Instance>, Ghost(block_size): Ghost<nat>, Ghost(heap_id): Ghost<Option<HeapId>>, ) -> LL
