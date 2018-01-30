open util/ordering[Time] as time
open util/ordering[SimpleAuction] as ord


sig Address {
}


sig Time {}

sig SimpleAuction {
	beneficiary: Address,
	auctionEnd: Time,
	highestBidder: lone Address,
	highestBid: lone Int,
	pendingReturns: Address -> Int,
	now: Time,
	ended: Int,

	account: Address -> one Int  // does not belong to auction, but easiest to handle
} {
	all a: Address | account[a] >= 0
}


fact traces {
	some beneficiary: Address, t: Time | newAuction[ord/first, t, beneficiary]
	// define all legal state transitions
	all a: SimpleAuction - ord/last |
		let a' = a.next |
			tick[a, a'] or 
			(some sender: Address, value: Int | bid[sender, a, a', value])
		    or (some sender: Address | withdraw[sender, a, a'])
			or auctionEnd[a, a']
}



pred newAuction(a: SimpleAuction, t: Time, b: Address) {
	a.beneficiary = b
	a.auctionEnd = t
	no a.highestBidder
	no a.highestBid	
	no a.pendingReturns
	a.now = time/first
	a.ended = 0
	// s.account may contain anything
}


pred tick(a, a': SimpleAuction) {
	a'.now = a.now.next
	// copy
	a'.beneficiary = a.beneficiary
	a'.auctionEnd = a.auctionEnd
	a'.highestBidder = a.highestBidder
	a'.highestBid = a.highestBid
	a'.pendingReturns = a.pendingReturns
	a'.ended = a.ended
	a'.account = a.account
}


pred bid(sender: Address, a, a': SimpleAuction, value: Int)  {
	// preconditions
	a.account[sender] >= value
	a.now in time/prevs[a.auctionEnd]
	value > a.highestBid
	
	// return previous bid
	not no a.highestBidder
    => a'.pendingReturns = a.pendingReturns ++ (a.highestBidder -> a.pendingReturns[a.highestBidder].plus[a.highestBid])
	else a'.pendingReturns = a.pendingReturns

	a'.highestBidder = sender
	a'.highestBid = value
	a'.account = a.account ++ (sender -> a.account[sender].minus[value])

	// copy
	a'.beneficiary = a.beneficiary
	a'.auctionEnd = a.auctionEnd
	a'.now = a.now
	a'.ended = a.ended
}


pred withdraw(sender: Address, a, a': SimpleAuction) {
	let pending = a.pendingReturns[sender] |
	pending > 0
	&& a'.account = a.account ++ (sender -> a.account[sender].plus[pending])

	a'.pendingReturns = a.pendingReturns ++ (sender -> 0)
	// copy
	a'.beneficiary = a.beneficiary
	a'.auctionEnd = a.auctionEnd
	a'.highestBidder = a.highestBidder
	a'.highestBid = a.highestBid
	a'.now = a.now
	a'.ended = a.ended
}


pred auctionEnd(a, a': SimpleAuction) {
	// preconditions
	a.now in time/nexts[a.auctionEnd] or a.now = a.auctionEnd
	a.ended = 0
	some a.highestBid  // THINK ABOUT

	a'.ended = 1
	// send money to beneficiary
	a'.account = a.account ++ (a.beneficiary -> a.account[a.beneficiary].plus[a.highestBid])
	
	// copy
	a'.beneficiary = a.beneficiary
	a'.auctionEnd = a.auctionEnd
	a'.highestBidder = a.highestBidder
	a'.highestBid = a.highestBid
	a'.now = a.now
	a'.pendingReturns = a.pendingReturns
}


fun accountSum[s: SimpleAuction] : Int {
	sum a: Address | s.account[a] 
}

// the EVM will make sure there is no new money
// but by checking this, we see that our contract does not even try
// to create new money
assert noNewMoney {
	let initialMoney = accountSum[ord/first] |
		all s: SimpleAuction | accountSum[s] <= initialMoney
}


fun allFunds(s:SimpleAuction, a: Address) : Int {
	s.account[a].plus[s.pendingReturns[a]]
}

fun initialAccount[a: Address] : Int {
	(ord/first).account[a]
}

assert bene {
	all s: SimpleAuction | 
	  let b = s.beneficiary|
      s.ended = 1 => 
       (s.highestBidder = s.beneficiary => allFunds[s, b] = initialAccount[b]
       else allFunds[s, b] = initialAccount[b].plus[s.highestBid])
}


check bene for 7

check noNewMoney for 5

run {
#Address >= 2 
some a: SimpleAuction | some a.highestBid
some a: SimpleAuction | a.ended = 1
some a, a': SimpleAuction, addr: Address | a' in ord/nexts[a] && a'.ended=0 && a'.account[addr] > a.account[addr]
 } for 8
