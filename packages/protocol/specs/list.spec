pragma specify 0.1

methods {
	getElementLesser(uint256) returns uint256 envfree
	getElementGreater(uint256) returns uint256 envfree
	getNumElements() returns uint256 envfree
	getTail() returns uint256 envfree
	getHead() returns uint256 envfree
	insert(uint256, uint256, uint256, uint256) envfree
	remove(uint256) envfree
	update(uint256, uint256, uint256, uint256) envfree
	contains(uint256) returns bool envfree
	getValue(uint256) returns uint256 envfree
	init_state()
}


invariant greaterContained(uint256 key) sinvoke contains(key) && sinvoke getElementGreater(key) != 0 => sinvoke contains(sinvoke getElementGreater(key))
{
	preserved remove(uint256 byeKey)
	{
		call basicRemoveInstances(byeKey);

		uint256 greater_key, lesser_key;
		call extraRemoveInstance(key, greater_key, lesser_key);
		requireInvariant greaterContained(key);
		requireInvariant greaterContained(lesser_key);
	}


	preserved update(uint256 updateKey, uint256 value, uint256 lesserKey, uint256 greaterKey)
	{
		uint256 greater_key_before = sinvoke getElementGreater(key);
		uint256 lesser_key_before = sinvoke getElementLesser(key);
		uint256 greater_updateKey = sinvoke getElementGreater(updateKey);
		uint256 lesser_updateKey = sinvoke getElementLesser(updateKey);
		requireInvariant hasHead();
		requireInvariant hasTwo(key, updateKey);
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(updateKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key_before);
		requireInvariant firstKey(lesser_key_before);
		requireInvariant firstKey(greater_updateKey);
		requireInvariant firstKey(lesser_updateKey);

		uint256 greater_lesser_key = sinvoke getElementGreater(lesserKey);
		uint256 greater_greater_key = sinvoke getElementGreater(greaterKey);
		uint256 lesser_lesser_key = sinvoke getElementLesser(lesserKey);
		uint256 lesser_greater_key = sinvoke getElementLesser(greaterKey);
		requireInvariant firstKey(greater_lesser_key);
		requireInvariant firstKey(greater_greater_key);
		requireInvariant firstKey(lesser_lesser_key);
		requireInvariant firstKey(lesser_greater_key);
		requireInvariant lastKey(greater_lesser_key);
		requireInvariant lastKey(greater_greater_key);
		requireInvariant lastKey(lesser_lesser_key);
		requireInvariant lastKey(lesser_greater_key);

		requireInvariant greaterContained(updateKey);
		requireInvariant lesserContained(updateKey);
		requireInvariant reciprocal1(updateKey);
		requireInvariant reciprocal2(updateKey);

		requireInvariant greaterContained(key);
		requireInvariant lesserContained(key);
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);

		requireInvariant reciprocal1(lesserKey);
		requireInvariant reciprocal2(lesserKey);
		requireInvariant reciprocal1(greaterKey);
		requireInvariant reciprocal2(greaterKey);

		requireInvariant reciprocal1(greater_updateKey);
		requireInvariant reciprocal1(lesser_updateKey);
		requireInvariant reciprocal2(greater_updateKey);
		requireInvariant reciprocal2(lesser_updateKey);
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(updateKey);
		requireInvariant lastKey(greater_key_before);
		requireInvariant lastKey(lesser_key_before);
		requireInvariant lastKey(greater_updateKey);
		requireInvariant lastKey(lesser_updateKey);

		requireInvariant isHead(key);
		requireInvariant isHead(updateKey);
		requireInvariant isHead(lesserKey);
		requireInvariant isHead(greaterKey);

		requireInvariant lesserContained(key);
		requireInvariant lesserContained(updateKey);
		requireInvariant greaterContained(key);
		requireInvariant greaterContained(updateKey);
	}

}


invariant lesserContained(uint256 key) sinvoke contains(key) && sinvoke getElementLesser(key) != 0 => sinvoke contains(sinvoke getElementLesser(key))
{
	preserved remove(uint256 byeKey)
	{
		uint256 greater_key = sinvoke getElementGreater(key);
		uint256 lesser_key = sinvoke getElementLesser(key);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key);
		requireInvariant firstKey(lesser_key);
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);
		requireInvariant lesserContained(key);
		requireInvariant lesserContained(lesser_key);


		call basicRemoveInstances(byeKey);

	}

	preserved update(uint256 updateKey, uint256 value, uint256 lesserKey, uint256 greaterKey)
	{
		uint256 greater_key_before = sinvoke getElementGreater(key);
		uint256 lesser_key_before = sinvoke getElementLesser(key);
		uint256 greater_updateKey = sinvoke getElementGreater(updateKey);
		uint256 lesser_updateKey = sinvoke getElementLesser(updateKey);
		requireInvariant hasHead();
		requireInvariant hasTwo(key, updateKey);
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(updateKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key_before);
		requireInvariant firstKey(lesser_key_before);
		requireInvariant firstKey(greater_updateKey);
		requireInvariant firstKey(lesser_updateKey);

		uint256 greater_lesser_key = sinvoke getElementGreater(lesserKey);
		uint256 greater_greater_key = sinvoke getElementGreater(greaterKey);
		uint256 lesser_lesser_key = sinvoke getElementLesser(lesserKey);
		uint256 lesser_greater_key = sinvoke getElementLesser(greaterKey);
		requireInvariant firstKey(greater_lesser_key);
		requireInvariant firstKey(greater_greater_key);
		requireInvariant firstKey(lesser_lesser_key);
		requireInvariant firstKey(lesser_greater_key);
		requireInvariant lastKey(greater_lesser_key);
		requireInvariant lastKey(greater_greater_key);
		requireInvariant lastKey(lesser_lesser_key);
		requireInvariant lastKey(lesser_greater_key);

		requireInvariant greaterContained(updateKey);
		requireInvariant lesserContained(updateKey);
		requireInvariant reciprocal1(updateKey);
		requireInvariant reciprocal2(updateKey);

		requireInvariant greaterContained(key);
		requireInvariant lesserContained(key);
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);

		requireInvariant reciprocal1(lesserKey);
		requireInvariant reciprocal2(lesserKey);
		requireInvariant reciprocal1(greaterKey);
		requireInvariant reciprocal2(greaterKey);

		requireInvariant reciprocal1(greater_updateKey);
		requireInvariant reciprocal1(lesser_updateKey);
		requireInvariant reciprocal2(greater_updateKey);
		requireInvariant reciprocal2(lesser_updateKey);
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(updateKey);
		requireInvariant lastKey(greater_key_before);
		requireInvariant lastKey(lesser_key_before);
		requireInvariant lastKey(greater_updateKey);
		requireInvariant lastKey(lesser_updateKey);

		requireInvariant isHead(key);
		requireInvariant isHead(updateKey);
		requireInvariant isHead(lesserKey);
		requireInvariant isHead(greaterKey);

		requireInvariant lesserContained(key);
		requireInvariant lesserContained(updateKey);
		requireInvariant greaterContained(key);
		requireInvariant greaterContained(updateKey);
	}

}



invariant reciprocal1(uint256 key) sinvoke contains(key) && sinvoke getElementLesser(key) != 0 => sinvoke getElementGreater(sinvoke getElementLesser(key)) == key
{
	preserved insert(uint256 newKey, uint256 value, uint256 newLesserKey, uint256 newGreaterKey) 
	{
		call basicInsertInstances(newKey, value, newLesserKey, newGreaterKey);
		requireInvariant firstKey(key);
		requireInvariant lesserContained(key);
		requireInvariant greaterContained(key);
		uint256 greater_key, lesser_key;
		call extraRemoveInstance(key, greater_key, lesser_key);


		/*
		uint256 greater_key = sinvoke getElementGreater(key);
		uint256 lesser_key = sinvoke getElementLesser(key);
		requireInvariant firstKey(greater_key);
		requireInvariant firstKey(lesser_key);
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);

		*/

		/*
		requireInvariant reciprocal1(newKey);
		requireInvariant reciprocal2(newKey);
		requireInvariant reciprocal1(newLesserKey);
		requireInvariant reciprocal2(newLesserKey);
		requireInvariant reciprocal1(newGreaterKey);
		requireInvariant reciprocal2(newGreaterKey);

		requireInvariant lesserContained(key);
		requireInvariant lesserContained(newKey);
		requireInvariant greaterContained(key);
		requireInvariant greaterContained(newKey);*/

	}

	preserved remove(uint256 byeKey)
	{
		call basicRemoveInstances(byeKey);
		uint256 greater_key, lesser_key;
		call extraRemoveInstance(key, greater_key, lesser_key);

		/*
			uint256 greater_key = sinvoke getElementGreater(key);
			uint256 lesser_key = sinvoke getElementLesser(key);
			requireInvariant firstKey(key);
			requireInvariant firstKey(greater_key);
			requireInvariant firstKey(lesser_key);
			requireInvariant reciprocal1(key);
			requireInvariant reciprocal2(key);
		*/

		/*
			uint256 greater_byeKey = sinvoke getElementGreater(byeKey);
			uint256 lesser_byeKey = sinvoke getElementLesser(byeKey);
			requireInvariant hasHead2();
			requireInvariant hasTail();
			requireInvariant hasTail2();
			requireInvariant firstKey(byeKey);
			requireInvariant firstKey(greater_byeKey);
			requireInvariant firstKey(lesser_byeKey);
			requireInvariant greaterContained(byeKey);
			requireInvariant lesserContained(byeKey);	
			requireInvariant reciprocal1(byeKey);
			requireInvariant reciprocal2(byeKey);
		*/

	}


	preserved update(uint256 updateKey, uint256 value, uint256 lesserKey, uint256 greaterKey)
	{
		uint256 greater_key_before = sinvoke getElementGreater(key);
		uint256 lesser_key_before = sinvoke getElementLesser(key);
		uint256 greater_updateKey = sinvoke getElementGreater(updateKey);
		uint256 lesser_updateKey = sinvoke getElementLesser(updateKey);
		requireInvariant hasHead();
		requireInvariant hasTwo(key, updateKey);
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(updateKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key_before);
		requireInvariant firstKey(lesser_key_before);
		requireInvariant firstKey(greater_updateKey);
		requireInvariant firstKey(lesser_updateKey);

		uint256 greater_lesser_key = sinvoke getElementGreater(lesserKey);
		uint256 greater_greater_key = sinvoke getElementGreater(greaterKey);
		uint256 lesser_lesser_key = sinvoke getElementLesser(lesserKey);
		uint256 lesser_greater_key = sinvoke getElementLesser(greaterKey);
		requireInvariant firstKey(greater_lesser_key);
		requireInvariant firstKey(greater_greater_key);
		requireInvariant firstKey(lesser_lesser_key);
		requireInvariant firstKey(lesser_greater_key);
		requireInvariant lastKey(greater_lesser_key);
		requireInvariant lastKey(greater_greater_key);
		requireInvariant lastKey(lesser_lesser_key);
		requireInvariant lastKey(lesser_greater_key);

		requireInvariant greaterContained(updateKey);
		requireInvariant lesserContained(updateKey);
		requireInvariant reciprocal1(updateKey);
		requireInvariant reciprocal2(updateKey);

		requireInvariant greaterContained(key);
		requireInvariant lesserContained(key);
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);

		requireInvariant reciprocal1(lesserKey);
		requireInvariant reciprocal2(lesserKey);
		requireInvariant reciprocal1(greaterKey);
		requireInvariant reciprocal2(greaterKey);

		requireInvariant reciprocal1(greater_updateKey);
		requireInvariant reciprocal1(lesser_updateKey);
		requireInvariant reciprocal2(greater_updateKey);
		requireInvariant reciprocal2(lesser_updateKey);
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(updateKey);
		requireInvariant lastKey(greater_key_before);
		requireInvariant lastKey(lesser_key_before);
		requireInvariant lastKey(greater_updateKey);
		requireInvariant lastKey(lesser_updateKey);

		requireInvariant isHead(key);
		requireInvariant isHead(updateKey);
		requireInvariant isHead(lesserKey);
		requireInvariant isHead(greaterKey);

		requireInvariant lesserContained(key);
		requireInvariant lesserContained(updateKey);
		requireInvariant greaterContained(key);
		requireInvariant greaterContained(updateKey);
	}
}


invariant reciprocal2(uint256 key) sinvoke contains(key) && sinvoke getElementGreater(key) != 0 => sinvoke getElementLesser(sinvoke getElementGreater(key)) == key
{
	
	preserved insert(uint256 newKey, uint256 value, uint256 newLesserKey, uint256 newGreaterKey) 
	{
		requireInvariant hasHead();
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(newKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(newGreaterKey);
		requireInvariant firstKey(newLesserKey);

		uint256 greater_key = sinvoke getElementGreater(key);
		uint256 lesser_key = sinvoke getElementLesser(key);


		requireInvariant firstKey(greater_key);
		requireInvariant firstKey(lesser_key);
		requireInvariant firstKey(sinvoke getElementLesser(newLesserKey));
		requireInvariant firstKey(sinvoke getElementLesser(newGreaterKey));
		requireInvariant containsNotZero();

		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);
		requireInvariant reciprocal1(newKey);
		requireInvariant reciprocal2(newKey);
		requireInvariant reciprocal1(newLesserKey);
		requireInvariant reciprocal2(newLesserKey);
		requireInvariant reciprocal1(newGreaterKey);
		requireInvariant reciprocal2(newGreaterKey);

		requireInvariant lesserContained(key);
		requireInvariant lesserContained(newKey);
		requireInvariant greaterContained(key);
		requireInvariant greaterContained(newKey);
	}

	preserved remove(uint256 byeKey)
	{
		/*
			uint256 greater_key = sinvoke getElementGreater(key);
			uint256 lesser_key = sinvoke getElementLesser(key);
			requireInvariant firstKey(key);
			requireInvariant firstKey(greater_key);
			requireInvariant firstKey(lesser_key);		
			requireInvariant reciprocal1(key);
			requireInvariant reciprocal2(key);

			uint256 greater_key = sinvoke getElementGreater(key);
			uint256 lesser_key = sinvoke getElementLesser(key);
			requireInvariant firstKey(key);
			requireInvariant firstKey(greater_key);
			requireInvariant firstKey(lesser_key);
			requireInvariant reciprocal1(key);
			requireInvariant reciprocal2(key);
		*/

		call basicRemoveInstances(byeKey);
		uint256 greater_key, lesser_key;
		call extraRemoveInstance(key, greater_key, lesser_key);

		/*

			uint256 greater_byeKey = sinvoke getElementGreater(byeKey);
			uint256 lesser_byeKey = sinvoke getElementLesser(byeKey);
			requireInvariant hasHead2();
			requireInvariant hasTail();
			requireInvariant hasTail2();
			requireInvariant firstKey(byeKey);
			requireInvariant firstKey(greater_byeKey);
			requireInvariant firstKey(lesser_byeKey);

			requireInvariant greaterContained(byeKey);
			requireInvariant lesserContained(byeKey);
			requireInvariant reciprocal1(byeKey);
			requireInvariant reciprocal2(byeKey);
		*/

	}


	preserved update(uint256 updateKey, uint256 value, uint256 lesserKey, uint256 greaterKey)
	{
		uint256 greater_key_before = sinvoke getElementGreater(key);
		uint256 lesser_key_before = sinvoke getElementLesser(key);
		uint256 greater_updateKey = sinvoke getElementGreater(updateKey);
		uint256 lesser_updateKey = sinvoke getElementLesser(updateKey);
		requireInvariant hasHead();
		requireInvariant hasTwo(key, updateKey);
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(updateKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key_before);
		requireInvariant firstKey(lesser_key_before);
		requireInvariant firstKey(greater_updateKey);
		requireInvariant firstKey(lesser_updateKey);

		uint256 greater_lesser_key = sinvoke getElementGreater(lesserKey);
		uint256 greater_greater_key = sinvoke getElementGreater(greaterKey);
		uint256 lesser_lesser_key = sinvoke getElementLesser(lesserKey);
		uint256 lesser_greater_key = sinvoke getElementLesser(greaterKey);
		requireInvariant firstKey(greater_lesser_key);
		requireInvariant firstKey(greater_greater_key);
		requireInvariant firstKey(lesser_lesser_key);
		requireInvariant firstKey(lesser_greater_key);
		requireInvariant lastKey(greater_lesser_key);
		requireInvariant lastKey(greater_greater_key);
		requireInvariant lastKey(lesser_lesser_key);
		requireInvariant lastKey(lesser_greater_key);

		requireInvariant greaterContained(updateKey);
		requireInvariant lesserContained(updateKey);
		requireInvariant reciprocal1(updateKey);
		requireInvariant reciprocal2(updateKey);

		requireInvariant greaterContained(key);
		requireInvariant lesserContained(key);
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);

		requireInvariant reciprocal1(lesserKey);
		requireInvariant reciprocal2(lesserKey);
		requireInvariant reciprocal1(greaterKey);
		requireInvariant reciprocal2(greaterKey);

		requireInvariant reciprocal1(greater_updateKey);
		requireInvariant reciprocal1(lesser_updateKey);
		requireInvariant reciprocal2(greater_updateKey);
		requireInvariant reciprocal2(lesser_updateKey);
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(updateKey);
		requireInvariant lastKey(greater_key_before);
		requireInvariant lastKey(lesser_key_before);
		requireInvariant lastKey(greater_updateKey);
		requireInvariant lastKey(lesser_updateKey);

		requireInvariant isHead(key);
		requireInvariant isHead(updateKey);
		requireInvariant isHead(lesserKey);
		requireInvariant isHead(greaterKey);

		requireInvariant lesserContained(key);
		requireInvariant lesserContained(updateKey);
		requireInvariant greaterContained(key);
		requireInvariant greaterContained(updateKey);
	}

}




// First invariant in document
invariant firstKey(uint256 key) sinvoke contains(key) => (sinvoke getElementGreater(key) == 0 <=> key == sinvoke getHead()) 
{
	preserved update(uint256 updateKey, uint256 value, uint256 lesserKey, uint256 greaterKey)
	{
		uint256 greater_key_before = sinvoke getElementGreater(key);
		uint256 lesser_key_before = sinvoke getElementLesser(key);
		uint256 greater_updateKey = sinvoke getElementGreater(updateKey);
		uint256 lesser_updateKey = sinvoke getElementLesser(updateKey);
		requireInvariant hasHead();
		requireInvariant hasTwo(key, updateKey);
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(updateKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key_before);
		requireInvariant firstKey(lesser_key_before);
		requireInvariant firstKey(greater_updateKey);
		requireInvariant firstKey(lesser_updateKey);

		uint256 greater_lesser_key = sinvoke getElementGreater(lesserKey);
		uint256 greater_greater_key = sinvoke getElementGreater(greaterKey);
		uint256 lesser_lesser_key = sinvoke getElementLesser(lesserKey);
		uint256 lesser_greater_key = sinvoke getElementLesser(greaterKey);
		requireInvariant firstKey(greater_lesser_key);
		requireInvariant firstKey(greater_greater_key);
		requireInvariant firstKey(lesser_lesser_key);
		requireInvariant firstKey(lesser_greater_key);
		requireInvariant lastKey(greater_lesser_key);
		requireInvariant lastKey(greater_greater_key);
		requireInvariant lastKey(lesser_lesser_key);
		requireInvariant lastKey(lesser_greater_key);

		requireInvariant greaterContained(updateKey);
		requireInvariant lesserContained(updateKey);
		requireInvariant reciprocal1(updateKey);
		requireInvariant reciprocal2(updateKey);

		requireInvariant greaterContained(key);
		requireInvariant lesserContained(key);
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);

		requireInvariant reciprocal1(lesserKey);
		requireInvariant reciprocal2(lesserKey);
		requireInvariant reciprocal1(greaterKey);
		requireInvariant reciprocal2(greaterKey);

		requireInvariant reciprocal1(greater_updateKey);
		requireInvariant reciprocal1(lesser_updateKey);
		requireInvariant reciprocal2(greater_updateKey);
		requireInvariant reciprocal2(lesser_updateKey);
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(updateKey);
		requireInvariant lastKey(greater_key_before);
		requireInvariant lastKey(lesser_key_before);
		requireInvariant lastKey(greater_updateKey);
		requireInvariant lastKey(lesser_updateKey);

		requireInvariant isHead(key);
		requireInvariant isHead(updateKey);
		requireInvariant isHead(lesserKey);
		requireInvariant isHead(greaterKey);
	}

	preserved remove(uint256 byeKey)
	{
		uint256 greater_key = sinvoke getElementGreater(key);
		uint256 lesser_key = sinvoke getElementLesser(key);
		uint256 greater_byeKey = sinvoke getElementGreater(byeKey);
		uint256 lesser_byeKey = sinvoke getElementLesser(byeKey);
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(byeKey);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key);
		requireInvariant firstKey(lesser_key);
		requireInvariant firstKey(greater_byeKey);
		requireInvariant firstKey(lesser_byeKey);

		requireInvariant greaterContained(byeKey);
		requireInvariant lesserContained(byeKey);
		
		requireInvariant reciprocal1(byeKey);
		requireInvariant reciprocal2(byeKey);

		requireInvariant reciprocal1(greater_byeKey);
		requireInvariant reciprocal1(lesser_byeKey);
		requireInvariant reciprocal2(greater_byeKey);
		requireInvariant reciprocal2(lesser_byeKey);
		requireInvariant containsNotZero();
		requireInvariant lastKey(key);
		requireInvariant lastKey(byeKey);
		requireInvariant lastKey(greater_key);
		requireInvariant lastKey(lesser_key);
		requireInvariant lastKey(greater_byeKey);
		requireInvariant lastKey(lesser_byeKey);
	}


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
}


invariant lastKey(uint256 key) sinvoke contains(key) => (sinvoke getElementLesser(key) == 0 <=> key == sinvoke getTail())

// 2nd invariant
// DIFFICULT ONE 
invariant hasHead() sinvoke getHead() == 0 <=> sinvoke getNumElements() == 0
invariant hasTwo(uint256 key1, uint256 key2) sinvoke contains(key1) && sinvoke contains(key2) && key1 != key2 => sinvoke getNumElements() >= 2

invariant isHead(uint256 key) sinvoke contains(key) => (sinvoke getHead() == key <=> sinvoke getElementGreater(key) == 0)

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

rule basicInsertInstances(uint256 newKey, uint256 value, uint256 newLesserKey, uint256 newGreaterKey) {
		requireInvariant hasHead();
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(newKey);
		requireInvariant firstKey(newGreaterKey);
		requireInvariant firstKey(newLesserKey);

		requireInvariant firstKey(sinvoke getElementLesser(newLesserKey));
		requireInvariant firstKey(sinvoke getElementLesser(newGreaterKey));
		requireInvariant containsNotZero();

		requireInvariant reciprocal1(newKey);
		requireInvariant reciprocal2(newKey);
		requireInvariant reciprocal1(newLesserKey);
		requireInvariant reciprocal2(newLesserKey);
		requireInvariant reciprocal1(newGreaterKey);
		requireInvariant reciprocal2(newGreaterKey);

		requireInvariant lesserContained(newKey);
		requireInvariant greaterContained(newKey);
}

rule basicRemoveInstances(uint256 byeKey)
{
		uint256 greater_byeKey = sinvoke getElementGreater(byeKey);
		uint256 lesser_byeKey = sinvoke getElementLesser(byeKey);
		requireInvariant hasHead2();
		requireInvariant hasTail();
		requireInvariant hasTail2();
		requireInvariant firstKey(byeKey);
		requireInvariant firstKey(greater_byeKey);
		requireInvariant firstKey(lesser_byeKey);
		requireInvariant greaterContained(byeKey);
		requireInvariant lesserContained(byeKey);
		requireInvariant reciprocal1(byeKey);
		requireInvariant reciprocal2(byeKey);
		requireInvariant containsNotZero();
		requireInvariant lesserContained(byeKey);
		requireInvariant lesserContained(greater_byeKey);
		requireInvariant lesserContained(lesser_byeKey);
}

rule extraRemoveInstance(uint256 key, uint256 greater_key, uint256 lesser_key) {
		require greater_key == sinvoke getElementGreater(key);
		require lesser_key == sinvoke getElementLesser(key);
		requireInvariant firstKey(key);
		requireInvariant firstKey(greater_key);
		requireInvariant firstKey(lesser_key);		
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);
}

rule basicInstances(uint256 key) {
		requireInvariant reciprocal1(key);
		requireInvariant reciprocal2(key);
		requireInvariant greaterContained(key);		
		requireInvariant lesserContained(key);		
		requireInvariant firstKey(key);	
		requireInvariant lastKey(key);
		requireInvariant isHead(key);
		assert true;
}