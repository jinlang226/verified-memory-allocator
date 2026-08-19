pub struct LL {
    first: *mut Node,

    data: Ghost<LLData>,

    // first to be popped off goes at the end
    perms: Tracked<Map<nat, (PointsTo<Node>, PointsToRaw, Mim::block, IsExposed)>>,
}
