open util/ordering[SystemState]

abstract sig Host {}
one sig Receiver extends Host {}
one sig Sender extends Host {}

abstract sig State {}
one sig Waiting, Receiving, Sending extends State {}
sig Packet {}

sig SystemState {
	succ: lone SystemState,
	receiver: Receiver,
	sender: Sender,
	status: Host -> State,
	buffers: Host -> set Packet,
	pipe: set Packet
}

pred SystemState.Init[] {
	all p: Packet | p not in this.pipe and p not in this.buffers[this.receiver] and p in this.buffers[this.sender]
	all h: Host | this.status[h] = Waiting
}

pred Transition[s, s' : SystemState] {
	SenderTransition[s, s'] and ReceiverTransition[s, s']
}

pred SenderTransition[s, s' : SystemState] {
	s.status[s.sender] = Waiting => s.buffers[s.sender] in s'.buffers[s.sender] and s'.buffers[s.sender] in s.buffers[s.sender]
	s.status[s.sender] = Sending => s'.buffers[s.sender] in s.buffers[s.sender] and #(s.buffers[s.sender] - s'.buffers[s.sender]) = 1 and (s.buffers[s.sender] - s'.buffers[s.sender]) in s'.pipe

	s.status[s.sender] = Waiting and (some p: Packet | p in s.buffers[s.sender]) => s'.status[s.sender] = Sending
	else s.status[s.sender] = Waiting => s'.status[s.sender] = Waiting
	else s.status[s.sender] = Sending => s'.status[s.sender] = Waiting
}

pred ReceiverTransition[s, s': SystemState] {
	s.status[s.receiver] = Waiting => s.buffers[s.receiver] in s'.buffers[s.receiver] and s'.buffers[s.receiver] in s.buffers[s.receiver]
	s.status[s.receiver] = Receiving => s.buffers[s.receiver] in s'.buffers[s.receiver] and (one p: Packet | p in s.pipe and p not in s'.pipe and p in s'.buffers[s.receiver])

	s.status[s.receiver] = Waiting and (some p:Packet | p in s.pipe) => s'.status[s.receiver] = Receiving
	else s.status[s.receiver] = Waiting => s'.status[s.receiver] = Waiting
	else s.status[s.receiver] = Receiving => s'.status[s.receiver] = Waiting
}

fact Ring {
	all s: SystemState - first | s in first.^succ and first not in first.^succ
	last.succ = none
}

fact States {
	no s: SystemState | s.status[s.receiver] = Sending
	no s: SystemState | s.status[s.sender] = Receiving
	all s: SystemState | #(s.status[s.receiver]) = 1 and #(s.status[s.sender]) = 1
	all s: SystemState | no p: Packet | p in s.buffers[Host] and p in s.pipe
}

fact Trace {
	first.Init[]
	all s : SystemState - last | Transition[s, s.succ]
}

assert NoReceive {
	no s: SystemState | s.status[s.receiver] = Sending or s.status[s.sender] = Receiving
}

pred show {}

pred sendAll {
	some s: SystemState | (no p: Packet | p in s.buffers[s.sender] or p in s.pipe)
}

run sendAll for 7 but 3 Packet

assert alwaysSends {
	no s: SystemState | s = last and not (no p: Packet | p in s.buffers[s.sender] or p in s.pipe)
}

check alwaysSends for 7 but 3 Packet
