open util/ordering[SystemState]

abstract sig Host {}
one sig Receiver extends Host {}
one sig Sender extends Host {}

abstract sig Header {}
one sig ACK, NAK, DATA extends Header {}

abstract sig State {}
one sig Waiting, Receiving, Sending, Acking extends State {}

sig Packet {
	checksum: one Checksum,
	data: lone Data,
	header: one Header,
	destination: one Host
}

sig Data {}

sig Checksum {}

fun generatePacket[d: Data, dest: Host, head: Header] : Packet {
	{p: Packet |p.data = d and p.checksum = generateChecksum[d] and p.header = head and p.destination = dest}
}

fun generateChecksum[d: Data] : Checksum {
	{c: Checksum}
}

sig SystemState {
	receiver: Receiver,
	sender: Sender,
	status: Host -> State,
	buffers: Host -> set Data,
	pipe: lone Packet,
	checksums: Data -> Checksum,
	lastSent : lone Data
}

pred SystemState.Init[] {
	all d: Data | d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all h: Host | this.status[h] = Waiting
	this.pipe = none
	this.lastSent = none
}

pred Transition[s, s' : SystemState] {
	s.status[Sender] = Waiting and s.status[Receiver] = Waiting => bothWaitingTransition[s,s']
	else s.status[Sender] = Sending and s.status[Receiver] = Waiting => sendPacketIntoPipeTransition[s,s']
	else s.status[Sender] = Waiting and s.status[Receiver] = Receiving => takePacketFromPipeTransition[s,s'] //shouldln't happen
	else s.status[Sender] = Sending and s.status[Receiver] = Receiving => swapPacketFromPipeTransition[s,s']//shouldln't happen
	else s.status[Sender] = Acking and s.status[Receiver] = Waiting => switchToReceivingTransition[s,s']
	else s.status[Sender] = Acking and s.status[Receiver] = Receiving => takePacketFromPipeSendAckTransition[s,s']
}

pred bothWaitingTransition[s,s' : SystemState] {
	s'.pipe = s.pipe
	s'.buffers = s.buffers
	s'.lastSent = s.lastSent

	(some s.buffers[Sender]) => s'.status[Sender] = Sending
	else s'.status[Sender] = Waiting

	(s.pipe not = none) and (s.pipe.destination = Receiver) => s'.status[Receiver] = Receiving
	else s'.status[Receiver] = Waiting
}

pred sendPacketIntoPipeTransition[s,s' : SystemState] {
	s'.status[Sender] = Acking
	s'.status[Receiver] = Waiting
	s'.buffers[Receiver] = s.buffers[Receiver]

	(one d: s.buffers[Sender] | s'.pipe = generatePacket[d, Receiver, DATA] and s'.pipe not = none and s'.buffers[Sender] = s.buffers[Sender] - d and s'.lastSent = d)
}

pred takePacketFromPipeTransition[s,s' : SystemState] {
	1=0
	/*s'.status[Sender] = s.status[Sender]
	s'.status[Receiver] = Waiting
	s'.buffers[Sender] = s.buffers[Sender]
	s'.pipe = none
	s'.buffers[Receiver] = s.buffers[Receiver] + s.pipe.data
	s'.lastSent = s.lastSent*/
}

pred swapPacketFromPipeTransition[s,s' : SystemState] {
	1=0
	/*s'.status[Sender] = Waiting
	s'.status[Receiver] = Waiting
	(one d: s.buffers[Sender] | s'.pipe = generatePacket[d, Receiver, DATA] and s'.pipe not = none and s'.buffers[Sender] = s.buffers[Sender] - d and s'.lastSent = d)
	s'.buffers[Receiver] = s.buffers[Receiver] + s.pipe.data*/
}

pred  switchToReceivingTransition[s,s' : SystemState]{
	s'.buffers = s.buffers
	(s.pipe not = none) and (s.pipe.destination = Sender) => s'.status[Sender] = Waiting and s'.pipe = none and s'.lastSent = none
	else s'.status[Sender]=Acking and s'.pipe = s.pipe and s'.lastSent = s.lastSent

	(s.pipe not = none) and (s.pipe.destination = Receiver) => s'.status[Receiver] = Receiving
	else s'.status[Receiver] = Waiting
}

pred takePacketFromPipeSendAckTransition[s,s' : SystemState]{
	s'.status[Sender] = Acking
	s'.status[Receiver] = Waiting
	s'.lastSent = s.lastSent
	s'.buffers[Sender] = s.buffers[Sender]
	s'.buffers[Receiver] = s.buffers[Receiver] + s.pipe.data
	s'.pipe = generatePacket[none,Sender,ACK]
}

fact States {
	no s: SystemState | s.status[s.receiver] = Sending or s.status[s.receiver] = Acking or s.status[s.sender] = Receiving
	all s: SystemState | #(s.status[s.receiver]) = 1 and #(s.status[s.sender]) = 1
	no disj p1, p2: Packet | p1.data = p2.data and p1.data not = none
}

fact Trace {
	first.Init[]
	all s : SystemState - last | Transition[s, s.next]
}

assert NoReceive {
	no s: SystemState | s.status[s.receiver] = Sending or s.status[s.sender] = Receiving
}

pred show {}
run show for 7 but exactly 1 Data, exactly 2 Packet

pred sendAll {
	some s: SystemState | (no d: Data | d in s.buffers[s.sender]) and (all d: Data | d in s.buffers[Receiver])
}

run sendAll for 10 but exactly 4 Packet, exactly 2 Data

assert alwaysSends {
	(no p: Packet | p in last.pipe) and (all d: Data | d in last.buffers[last.receiver])
}

check alwaysSends for 7 but exactly 2 Packet, exactly 2 Data

run Transition for 1 but exactly 3 SystemState
run Init for 1
