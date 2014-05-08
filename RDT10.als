open util/ordering[SystemState]

abstract sig Host {}
one sig Receiver extends Host {}
one sig Sender extends Host {}

abstract sig State {}
one sig Waiting, Receiving, Sending extends State {}
sig Packet {}
sig Data {}

sig SystemState {
	succ: lone SystemState,
	receiver: Receiver,
	sender: Sender,
	status: Host -> State,
	buffers: Host -> set Data,
	pipe: Packet -> lone Data
}

pred SystemState.Init[] {
	all p: Packet | no this.pipe[p]
	all d: Data | d in this.buffers[this.sender] and d not in this.buffers[this.receiver] and no p: Packet | d in this.pipe[p]
	all h: Host | this.status[h] = Waiting
}

pred Transition[s, s' : SystemState] {
	SenderTransition[s, s'] and ReceiverTransition[s, s']

	s.status[s.receiver] = Waiting and s.status[s.sender]  = Waiting => s.pipe in s'.pipe and s'.pipe in s.pipe
	else s.status[s.receiver] = Receiving and s.status[s.sender] = Waiting => s'.pipe in s.pipe
	else s.status[s.receiver] = Waiting and s.status[s.sender] = Sending => s.pipe in s'.pipe
	else s.status[s.receiver] = Receiving and s.status[s.sender] = Sending => #(s.pipe - s'.pipe) = 1 and #(s'.pipe - s.pipe) = 1
}

pred SenderTransition[s, s' : SystemState] {
	s.status[s.sender] = Waiting => s.buffers[s.sender] in s'.buffers[s.sender] and s'.buffers[s.sender] in s.buffers[s.sender]
	s.status[s.sender] = Sending => one d: Data | d in s.buffers[s.sender] and d not in s'.buffers[s.sender] and (one p: Packet | s'.pipe[p] = d) and #(s.buffers[s.sender] - s'.buffers[s.sender]) = 1

	s.status[s.sender] = Waiting and (some d: Data | d in s.buffers[s.sender]) => s'.status[s.sender] = Sending
	else s.status[s.sender] = Waiting => s'.status[s.sender] = Waiting
	else s.status[s.sender] = Sending => s'.status[s.sender] = Waiting
}

pred ReceiverTransition[s, s': SystemState] {
	s.status[s.receiver] = Waiting => s.buffers[s.receiver] in s'.buffers[s.receiver] and s'.buffers[s.receiver] in s.buffers[s.receiver]
	s.status[s.receiver] = Receiving => s.buffers[s.receiver] in s'.buffers[s.receiver] and (one p: Packet | one s.pipe[p] and no s'.pipe[p] and s.pipe[p] in s'.buffers[s.receiver])

	s.status[s.receiver] = Waiting and (some p:Packet | some s.pipe[p]) => s'.status[s.receiver] = Receiving
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
	all s: SystemState | all p: Packet | no d: Data | s.pipe[p] = d and d in s.buffers[Host]
}

fact Trace {
	first.Init[]
	all s : SystemState - last | Transition[s, s.succ]
}

assert NoReceive {
	no s: SystemState | s.status[s.receiver] = Sending or s.status[s.sender] = Receiving
}

pred show {}
run show for 5 but exactly 1 Data, exactly 1 Packet

pred sendAll {
	//some s: SystemState | (no p: Packet | p in s.buffers[s.sender] or p in s.pipe)
	some s: SystemState | (no d: Data | d in s.buffers[s.sender] or (some p: Packet | d in s.pipe[p]))
}

run sendAll for 7 but exactly 2 Packet, exactly 2 Data

assert alwaysSends {
	(no p: Packet | some last.pipe[p]) and (all d: Data | d in last.buffers[last.receiver])
}

check alwaysSends for 7 but exactly 2 Packet, exactly 2 Data
