open util/ordering[Ballot] as ord


// represents the identity of a voter
sig Address {}


sig Proposal {}


sig Ballot {
	weight: Address -> lone Int,
	voted: set Address,  // also contains delegators
	vote: Address -> Proposal,
	delegate: Address -> Address,
	count: Proposal ->  Int,
	chairperson: Address
}

fact traces {
	// the first state is a freshly created ballot
	some chairperson: Address | freshBallot[chairperson, ord/first]
	// define all legal state transitions
	all b: Ballot - ord/last |
		let b' = b.next |
			(some sender, voter: Address | giveRightToVote[sender, b, b', voter])
			or (some sender, to: Address | delegate[sender, b, b', to])
		    or (some sender: Address, prop: Proposal | vote[sender, b, b', prop])
}


// new ballot created by the sender
pred freshBallot(sender: Address, ballot: Ballot) {
	no ballot.voted
	all p: Proposal | ballot.count[p] = 0
	no ballot.weight[Address]
	no ballot.delegate[Address]
	no ballot.vote[Address]
	ballot.chairperson = sender
}


// "sender" gives "voter" the right to vote
// b' is the resulting ballot copy
pred giveRightToVote(sender: Address, b, b': Ballot, voter: Address) {
	// preconditions
    sender = b.chairperson
	voter not in b.voted
	voter not in b.weight.Int

	// copy
    b'.voted = b.voted
	b'.count = b.count
	b'.chairperson = b.chairperson
	b'.delegate = b.delegate
    b'.vote = b.vote
	
	// change
	b'.weight = b.weight + voter -> 1
}


// "sender" delegates its voting right to "to"
pred delegate(sender: Address, b, b': Ballot, to: Address) {
	// preconditions
	sender not in b.voted
	// b.weight[sender] > 0  // NEW: you should only delegate if you have the right to vote 
									 // SOMEWHAT CRITICAL: if you delegate and are afterwards given the right to vote,
									 // your vote will not count
    // TODO: fix giveRightToVote instead
	//b.weight[to] > 0  // NEW: you can only delegate to someone who has the right to vote
                               // QUITE CRITICAL: (1) if the delegate is given the right afterwards, it will only count as one vote
                               // (2) someone can gain the right to vote by delegation (but this might be by design)
	// copy
	b'.chairperson = b.chairperson
	b'.vote = b.vote
	// changes
	let delegates = to.*(b.delegate) |
	let finalDelegate = delegates - b.delegate.Address | 
		one finalDelegate
 		&& sender not in delegates
		&& b'.delegate = b.delegate + sender -> finalDelegate
        && (finalDelegate in b.voted => 
					increaseCountFromDelegate[sender, b, b', finalDelegate]
               else 
					increaseWeightFromDelegate[sender, b, b', finalDelegate]
            )
    b'.voted = b.voted + sender
}


// private
pred increaseCountFromDelegate[sender: Address, b, b': Ballot,  delegate: Address] {
	let proposal = b.vote[delegate] |
	let senderWeight = b.weight[sender] | 
	let oldCount = b.count[proposal] |
	    b'.count = b.count ++ (proposal -> (oldCount.plus[senderWeight]))
        && b'.weight = b.weight
}


// private
pred increaseWeightFromDelegate[sender: Address, b, b': Ballot,  delegate: Address] {
	let senderWeight = b.weight[sender] | 
		b'.weight = b.weight ++ (delegate -> b.weight[delegate].plus[senderWeight])
		&& b'.count = b.count
}


pred vote(sender: Address, b, b': Ballot, p: Proposal) {
	// preconditions
	sender not in b.voted
	b.weight[sender] > 0  // NEW: you should only vote if you have the right to vote (not critical)
	// copy
	b'.chairperson = b.chairperson
	b'.weight = b.weight
	b'.delegate = b.delegate
	// change
	b'.voted = b.voted + sender
	b'.vote = b.vote + sender -> p
	let senderWeight = b.weight[sender] |
		b'.count = b.count ++ (p -> b.count[p].plus[senderWeight])
}


// ASSERTIONS

// the count is the same, regardless of order of delegate vs vote
assert delegateVoteOrder {
	all b0, b1, b2, b3, b4: Ballot, p: Proposal, a0, a1: Address |
         (ballotWithTwoVoters[a0, b0, a0, a1]
         && delegate[a0, b0, b1, a1]
         && vote[a1, b1, b2, p]
		 && vote[a1, b0, b3, p]
         && delegate[a0, b3, b4, a1])
		 => b2.count = b4.count
}
pred ballotWithTwoVoters(sender: Address, b2: Ballot, a0, a1: Address) {
	some b0, b1: Ballot |
         freshBallot[sender, b0]
		 && giveRightToVote[sender, b0, b1, a0]
		 && giveRightToVote[sender, b1, b2, a1]
}


// you can either vote or delegate or noting; but not both
assert noVoteAndDelegate {
	all b: Ballot |
		let voters = b.vote.Proposal |
		let delegaters = b.delegate.Address |
			no voters & delegaters
}


// obviously, there should never be more counted votes than weights
// (but there can be fewer)
assert sumOfCountsNotMoreThanWeights {
	all b: Ballot |
		let counts = sum p: Proposal | b.count[p] |
		let weights = sum a: Address | b.weight[a] |
			counts <= weights
}


// delegation to self should not be possible (neither directly nor indirectly)
assert noLoopingDelegation {
	all b: Ballot |
		all a: Address | 
			a not in a.^(b.delegate)
}


check delegateVoteOrder for 8
check noVoteAndDelegate for 6 but 4 Int
check sumOfCountsNotMoreThanWeights for 3 but 6 Ballot
check noLoopingDelegation for 6 but 4 Int

// example traces
run {} for 3 but 6 Ballot
