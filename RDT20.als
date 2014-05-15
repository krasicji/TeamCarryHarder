open util/ordering[SystemState]

abstract sig Host {}
one sig Receiver extends Host {}
one sig Sender extends Host {}


abstract sig State {}
one sig Waiting, Receiving, Sending, Acking extends State {}

sig Packet {
	checksum: one Checksum,
	data: one Data,
	destination: one Host
}

sig Data {}
one sig Ack, Nak extends Data {}

sig Checksum {}

fun generatePacket[d: Data, dest: Host] : Packet {
	{p: Packet |p.data = d and p.destination = dest}
}

/*fun generateChecksum[d: Data] : Checksum {
	Global.checksums[d]
}*/

sig SystemState {
	receiver: Receiver,
	sender: Sender,
	status: Host -> State,
	buffers: Host -> set Data,
	pipe: lone Packet,
	lastSent : lone Data
}

one sig Global {
  checksums: Data one -> one Checksum
}


pred SystemState.Init[] {
	all d: Data - Ack - Nak| d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all d: Ack + Nak | d not in this.buffers[Host]
	all h: Host | this.status[h] = Waiting
	this.pipe = none
	this.lastSent = none
	all p: Packet | p.checksum = Global.checksums[p.data]
}

pred SystemState.InitWithOneError[] {
	all d: Data - Ack - Nak| d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all d: Ack + Nak | d not in this.buffers[Host]
	all h: Host | this.status[h] = Waiting
	this.pipe = none
	this.lastSent = none
	one disj p1,p2: Packet | p1.data = p2.data and p1.checksum not = p2.checksum and p1.checksum = Global.checksums[p1.data] and p1.data not in Ack + Nak and (all p: Packet - p1 - p2 | p.checksum = Global.checksums[p.data])
}

pred Transition[s, s' : SystemState] {
	s.status[Sender] = Waiting and s.status[Receiver] = Waiting => bothWaitingTransition[s,s']
	else s.status[Sender] = Sending and s.status[Receiver] = Waiting => sendPacketIntoPipeTransition[s,s']
	else s.status[Sender] = Waiting and s.status[Receiver] = Receiving => takePacketFromPipeTransition[s,s'] //shouldn't happen
	else s.status[Sender] = Sending and s.status[Receiver] = Receiving => swapPacketFromPipeTransition[s,s']//shouldn't happen
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

	(one d: s.buffers[Sender] | s'.pipe = generatePacket[d, Receiver] and s'.pipe not = none and s'.buffers[Sender] = s.buffers[Sender] - d and s'.lastSent = d)
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
	(s.pipe not = none) and (s.pipe.destination = Sender) and (s.pipe.data = Ack) => s'.status[Sender] = Waiting and s'.pipe = none and s'.lastSent = none
	else (s.pipe not = none) and (s.pipe.destination = Sender) and (s.pipe.data = Nak) => s'.status[Sender] = Acking and s'.pipe = generatePacket[s.lastSent, Receiver] and s'.lastSent = s.lastSent
	else s'.status[Sender]=Acking and s'.pipe = s.pipe and s'.lastSent = s.lastSent

	(s.pipe not = none) and (s.pipe.destination = Receiver) => s'.status[Receiver] = Receiving
	else s'.status[Receiver] = Waiting
}

pred takePacketFromPipeSendAckTransition[s,s' : SystemState]{
	s'.status[Sender] = Acking
	s'.status[Receiver] = Waiting
	s'.lastSent = s.lastSent
	s'.buffers[Sender] = s.buffers[Sender]
	s.pipe.checksum = Global.checksums[s.pipe.data] => s'.buffers[Receiver] = s.buffers[Receiver] + s.pipe.data and s'.pipe = generatePacket[Ack, Sender]
	else s'.buffers[Receiver] = s.buffers[Receiver] and s'.pipe = generatePacket[Nak, Sender]
	
	s'.pipe not = none
}

fact States {
	no s: SystemState | s.status[s.receiver] = Sending or s.status[s.receiver] = Acking or s.status[s.sender] = Receiving
	all s: SystemState | #(s.status[s.receiver]) = 1 and #(s.status[s.sender]) = 1
	//no disj p1, p2: Packet | p1.data = p2.data and p1.checksum = p2.checksum and p1.data not = none
	all p: Packet | p.data in Ack + Nak => p.destination = Sender
	all p: Packet | p.data in Data - Ack - Nak => p.destination = Receiver
}

pred Trace {
	first.Init[]
	all s : SystemState - last | Transition[s, s.next]
}

pred TraceWithOneError {
	first.InitWithOneError[]
	all s : SystemState - last | Transition[s, s.next]
}

assert NoReceive {
	no s: SystemState | s.status[s.receiver] = Sending or s.status[s.sender] = Receiving
}

pred show {
	TraceWithOneError
}
run show for 20 but exactly 4 Data, exactly 5 Packet

pred sendAll {
	Trace
	some s: SystemState | (no d: Data - Ack - Nak| d in s.buffers[s.sender]) and (all d: Data - Ack - Nak | d in s.buffers[Receiver])
}

run sendAll for 10 but exactly 4 Packet, exactly 4 Data

pred sendAllWithOneError {
	TraceWithOneError[]
	some s: SystemState | (no d: Data - Ack - Nak | d in s.buffers[s.sender]) and (all d : Data - Ack - Nak | d in s.buffers[Receiver])
}

run sendAllWithOneError for 20 but exactly 5 Packet, exactly 4 Data

assert alwaysSends {
	(no p: Packet | p in last.pipe) and (all d: Data | d in last.buffers[last.receiver]) and (last.status[Sender] = Waiting and last.status[Receiver] = Waiting)
}

check alwaysSends for 7 but exactly 3 Packet, exactly 1 Data

pred test {
	one disj s1, s2 : SystemState | s1.pipe = {p : Packet | p.destination = Receiver and p.data not in Ack + Nak} and s1.status[Receiver] = Receiving and s1.status[Sender] = Acking and takePacketFromPipeSendAckTransition[s1,s2]
}

run test for 2 but exactly 3 Data, exactly 3 Packet

run Transition for 1 but exactly 3 SystemState
run Init for 1
