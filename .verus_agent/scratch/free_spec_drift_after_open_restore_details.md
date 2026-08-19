verus-mimalloc/free.rs::free_generic mode=exec new=False removed=False impacted=[]
  - requires added: before= after=old(local).wf()
  - requires added: before= after=dealloc.mim_instance == old(local).inst()
  - ensures added: before= after=final(local).inst() == old(local).inst()
  - ensures added: before= after=final(local).wf()
  - ensures added: before= after=forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local))
verus-mimalloc/page.rs::page_retire mode=exec new=False removed=False impacted=[]
  - requires added: before= after=old(local).wf()
  - ensures added: before= after=final(local).inst() == old(local).inst()
  - ensures added: before= after=final(local).wf()
  - ensures added: before= after=forall |heap: HeapPtr| heap.is_in(*old(local)) ==> heap.is_in(*final(local))
