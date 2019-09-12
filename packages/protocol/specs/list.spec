pragma specify 0.1

methods {
	getElementLesser(uint256) returns uint256 consistent
	getElementGreater(uint256) returns uint256 consistent
	getNumElements() returns uint256 consistent
	getTail() returns uint256 consistent
	getHead() returns uint256 consistent
	insert(uint256, uint256, uint256, uint256) consistent
	remove(uint256) consistent
	update(uint256, uint256, uint256, uint256) consistent
	contains(uint256) returns bool consistent
	getValue(uint256) returns uint256 consistent
}

invariant numElementsNonEmpty(uint256 key) sinvoke contains(key) => sinvoke getNumElements() > 0
invariant firstKey(uint256 key) sinvoke contains(key) => (sinvoke getElementGreater(key) == 0 <=> key == sinvoke getHead())
invariant lastKey(uint256 key) sinvoke contains(key) => (sinvoke getElementLesser(key) == 0 <=> key == sinvoke getTail())
invariant containsNotZero(uint256 key) sinvoke contains(key) => key != 0
invariant hasHead() sinvoke getHead() == 0 <=> sinvoke getNumElements() == 0
invariant hasTail() sinvoke getTail() == 0 <=> sinvoke getNumElements() == 0
invariant sortedTail(uint256 key) sinvoke contains(key) => sinvoke getValue(sinvoke getTail()) <= sinvoke getValue(key)
invariant sortedHead(uint256 key) sinvoke contains(key) => sinvoke getValue(sinvoke getHead()) >= sinvoke getValue(key)

