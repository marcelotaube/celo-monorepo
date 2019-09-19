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

// First invariant in document
invariant firstKey(uint256 key) sinvoke contains(key) => (sinvoke getElementGreater(key) == 0 <=> key == sinvoke getHead()) 
{
	preserved insert(uint256 newKey, uint256 value, uint256 lesserKey, uint256 greaterKey) 
	{
		requireInvariant hasHead();
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(newKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greaterKey);
		requireInvariant firstKey(lesserKey);
		requireInvariant firstKey(sinvoke getElementGreater(lesserKey));
		requireInvariant firstKey(sinvoke getElementGreater(greaterKey));
		requireInvariant firstKey(sinvoke getElementLesser(lesserKey));
		requireInvariant firstKey(sinvoke getElementLesser(greaterKey));
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(newKey);
		requireInvariant lastKey(lesserKey);
		requireInvariant lastKey(greaterKey);
		requireInvariant lastKey(sinvoke getElementGreater(lesserKey));
		requireInvariant lastKey(sinvoke getElementGreater(greaterKey));
		requireInvariant lastKey(sinvoke getElementLesser(lesserKey));
		requireInvariant lastKey(sinvoke getElementLesser(greaterKey));
		requireInvariant sortedLesser(key);
		requireInvariant sortedLesser(newKey);
		requireInvariant sortedLesser(greaterKey);
		requireInvariant sortedLesser(lesserKey);
		requireInvariant sortedGreater(key);
		requireInvariant sortedGreater(newKey);
		requireInvariant sortedGreater(greaterKey);
		requireInvariant sortedGreater(lesserKey);
	}

	preserved remove(uint256 byeKey)
	{
		requireInvariant hasHead();
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(byeKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(sinvoke getElementGreater(byeKey));
		requireInvariant firstKey(sinvoke getElementLesser(byeKey));
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(byeKey);
		requireInvariant lastKey(sinvoke getElementGreater(byeKey));
		requireInvariant lastKey(sinvoke getElementLesser(byeKey));
		requireInvariant sortedLesser(key);
		requireInvariant sortedLesser(byeKey);
		requireInvariant sortedGreater(key);
		requireInvariant sortedGreater(byeKey);
	}


	preserved update(uint256 updateKey, uint256 value, uint256 lesserKey, uint256 greaterKey)
	{
		uint256 oldLesser = sinvoke getElementLesser(updateKey);
		uint256 oldGreater = sinvoke getElementGreater(updateKey);
		requireInvariant hasHead();
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(updateKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greaterKey);
		requireInvariant firstKey(lesserKey);
		requireInvariant firstKey(oldLesser);
		requireInvariant firstKey(oldGreater);
		requireInvariant firstKey(sinvoke getElementGreater(lesserKey));
		requireInvariant firstKey(sinvoke getElementGreater(greaterKey));
		requireInvariant firstKey(sinvoke getElementLesser(lesserKey));
		requireInvariant firstKey(sinvoke getElementLesser(greaterKey));
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(updateKey);
		requireInvariant lastKey(lesserKey);
		requireInvariant lastKey(greaterKey);
		requireInvariant lastKey(oldLesser);
		requireInvariant lastKey(oldGreater);
		requireInvariant lastKey(sinvoke getElementGreater(lesserKey));
		requireInvariant lastKey(sinvoke getElementGreater(greaterKey));
		requireInvariant lastKey(sinvoke getElementLesser(lesserKey));
		requireInvariant lastKey(sinvoke getElementLesser(greaterKey));
		requireInvariant sortedLesser(key);
		requireInvariant sortedLesser(updateKey);
		requireInvariant sortedLesser(greaterKey);
		requireInvariant sortedLesser(lesserKey);
		requireInvariant sortedLesser(oldLesser);
		requireInvariant sortedLesser(oldGreater);
		requireInvariant sortedGreater(key);
		requireInvariant sortedGreater(updateKey);
		requireInvariant sortedGreater(greaterKey);
		requireInvariant sortedGreater(oldLesser);
		requireInvariant sortedGreater(oldGreater);
		requireInvariant sortedGreater(lesserKey);
	}
}

invariant lastKey(uint256 key) sinvoke contains(key) => (sinvoke getElementLesser(key) == 0 <=> key == sinvoke getTail())

// 2nd invariant
// DIFFICULT ONE 
invariant hasHead() sinvoke getHead() == 0 <=> sinvoke getNumElements() == 0
invariant hasHead2() sinvoke getHead() != 0 <=> sinvoke contains(sinvoke getHead())


// 3rd
invariant hasTail() sinvoke getHead() == 0 <=> sinvoke getTail() == 0
invariant hasTail2() sinvoke getTail() != 0 <=> sinvoke contains(sinvoke getTail())

// 4th
invariant containsNotZero() !sinvoke contains(0)

// 5th
invariant sortedTail(uint256 key) sinvoke contains(key) => sinvoke getValue(sinvoke getTail()) <= sinvoke getValue(key)
invariant sortedHead(uint256 key) sinvoke contains(key) => sinvoke getValue(sinvoke getHead()) >= sinvoke getValue(key)

// more
invariant sortedGreater(uint256 key) sinvoke contains(key) && sinvoke getElementGreater(key) != 0 =>  sinvoke getValue(key) <= sinvoke getValue(sinvoke getElementGreater(key))
invariant sortedLesser(uint256 key) sinvoke contains(key) && sinvoke getElementLesser(key) != 0 =>  sinvoke getValue(key) >= sinvoke getValue(sinvoke getElementLesser(key))

