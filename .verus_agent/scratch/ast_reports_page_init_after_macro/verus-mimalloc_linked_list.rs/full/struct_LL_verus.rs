pub struct LL {
    pub(crate) first: *mut Node,

    pub(crate) data: Ghost<LLData>,

    // first to be popped off goes at the end
    pub(crate) perms: Tracked<Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>>,
}
