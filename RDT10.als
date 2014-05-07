open util/ordering[SystemState]

abstract sig Host {
	buffer: set Packet,
}
one sig Receiver extends Host {}
one sig Sender extends Host {}

abstract sig State {}
one sig Waiting, Receiving, Sending extends State {}

sig SystemState {
	succ: lone SystemState,
	receiver: Receiver,
	sender: Sender,
	status: Host -> State,
	pipe: set Packet
}

pred SystemState.Init[] {
	all p: Packet | p not in this.pipe and p not in this.receiver.buffer and p in this.sender.buffer
	all h: Host | this.status[h] = Waiting
}

pred Transition[s, s' : SystemState] {
	s.status[s.sender] = Waiting => s'.status[s.sender] = Sending
	else s.status[s.sender] = Sending => s'.status[s.sender] = Waiting

	s.status[s.receiver] = Waiting and some p:Packet | p in s.pipe => s'.status[s.receiver] = Receiving
	else s.status[s.receiver] = Receiving => s'.status[s.receiver] = Waiting
}

fact Ring {
	all s: SystemState - first | s in first.^succ and first not in first.^succ
	last.succ = none
}

fact States {
	no s: SystemState | s.status[Receiver] = Sending
	no s: SystemState | s.status[Sender] = Receiving
}

fact Trace {
	first.Init[]
	all s : SystemState - last | Transition[s, s.succ]
}

sig Packet {}

pred show {}
run show for 3 but exactly 3 Packet
