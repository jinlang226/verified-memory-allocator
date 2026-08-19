    pub fn empty() -> (ll: LL) ensures ll.wf(),
            ll.len() == 0,
            ll.first_addr() == 0,
            ll.ptr().addr() == 0,
    {
        LL::new(Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()), Ghost(arbitrary()))
    }
