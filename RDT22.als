open util/ordering[SystemState]

abstract sig Host {}
one sig Receiver extends Host {}
one sig Sender extends Host {}


abstract sig State {}
one sig Waiting, Receiving, Sending, Acking extends State {}

sig Packet {
	checksum: one Checksum,
	data: one Data,
	sequence: Int
}

sig Data {}
one sig Ack extends Data {}

sig Checksum {}

fun generateCorrectDataPacket[d: Data, s: Int] : Packet {
	{p: Packet |p.data = d and p.checksum = Global.checksums[d] and p.sequence = s}
}

fun generateIncorrectDataPacket[d: Data, s: Int] : Packet {
	{p: Packet |p.data = d and not p.checksum = Global.checksums[d] and p.sequence = s}
}

fun generateResponsePacket[d: Data, s: Int] : Packet {
	{p: Packet |p.data = d and p.sequence = s}
}

sig SystemState {
	receiver: Receiver,
	sender: Sender,
	status: Host -> State,
	buffers: Host -> set Data,
	pipe: lone Packet,
	lastSent : lone Data,
	lastReceived: Int,
	lastSentSequence: Int
}

fun SystemState.getNextNumber[] : Int {
	this.lastReceived = 0 => 1
	else 0
}

one sig Global {
  checksums: Data one -> one Checksum
}

pred SystemState.Init[] {
	all d: Data - Ack | d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all h: Host | this.status[h] = Waiting
	no this.pipe
	no this.lastSent
	all p: Packet | p.checksum = Global.checksums[p.data] or one p2: Packet | p.data = p2.data and p.checksum not = p2.checksum and p2.checksum = Global.checksums[p.data] and p.data not in Ack and (p.sequence = 0 or p.sequence = 1)
	this.lastReceived = 1
	this.lastSentSequence = 1
}

pred SystemState.InitCorruptAck[] {
	all d: Data - Ack| d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all h: Host | this.status[h] = Waiting
	no this.pipe
	no this.lastSent
}

pred Transition[s, s' : SystemState] {
	s.status[Sender] = Waiting and s.status[Receiver] = Waiting => bothWaitingTransition[s,s']
	else s.status[Sender] = Sending and s.status[Receiver] = Waiting => sendPacketIntoPipeTransition[s,s']
	else s.status[Sender] = Acking and s.status[Receiver] = Waiting => switchToReceivingTransition[s,s']
	else s.status[Sender] = Acking and s.status[Receiver] = Receiving => takePacketFromPipeSendAckTransition[s,s']
}

fact {
	#{Ack.~data} = 2
	no d: Ack | d in SystemState.buffers[Host]
	no p: Packet | p.sequence not = 0 and p.sequence not = 1
	one p: Packet | p.data = Ack and p.sequence = 0 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Ack and p.sequence = 1 and p.checksum = Global.checksums[p.data]
}

pred bothWaitingTransition[s,s' : SystemState] {
	s'.pipe = s.pipe
	s'.buffers = s.buffers
	s'.lastSent = s.lastSent
	s'.lastReceived = s.lastReceived
	s'.lastSentSequence = s.lastSentSequence

	(some s.buffers[Sender]) => s'.status[Sender] = Sending
	else s'.status[Sender] = Waiting

	(s.pipe not = none) and (s.pipe.data in Data - Ack) => s'.status[Receiver] = Receiving
	else s'.status[Receiver] = Waiting

	//Force the exact number of states to generate an instance
	s.pipe = none and s.buffers[Sender] = none => 1 = 0
}

pred sendPacketIntoPipeTransition[s,s' : SystemState] {
	s'.status[Sender] = Acking
	s'.status[Receiver] = Waiting
	s'.buffers[Receiver] = s.buffers[Receiver]
	s'.lastReceived = s.lastReceived

	(one d: s.buffers[Sender] | (s'.pipe = generateIncorrectDataPacket[d, s.getNextNumber[]] or s'.pipe = generateCorrectDataPacket[d, s.getNextNumber[]]) and s'.pipe not = none and s'.buffers[Sender] = s.buffers[Sender] - d and s'.lastSent = d)
	s'.lastSentSequence = s.getNextNumber[]
}

pred  switchToReceivingTransition[s,s' : SystemState]{
	s'.buffers = s.buffers
	s'.lastReceived = s.lastReceived
	s'.lastSentSequence = s.lastSentSequence
	(s.pipe not = none) and (s.pipe.data = Ack) and (s.pipe.checksum = Global.checksums[s.pipe.data]) and (s.pipe.sequence = s.lastSentSequence) => s'.status[Sender] = Waiting and s'.pipe = none and s'.lastSent = none
	else (s.pipe not = none) and (s.pipe.data = Ack) => s'.status[Sender] = Acking and s'.lastSent = s.lastSent and (s'.pipe = generateCorrectDataPacket[s.lastSent, s.lastSentSequence] or s'.pipe = generateIncorrectDataPacket[s.lastSent, s.lastSentSequence])
	//else (s.pipe not = none) and (s.pipe.data = Nak) and (s.pipe.checksum = Global.checksums[s.pipe.data]) => s'.status[Sender] = Acking and (s'.pipe = generateIncorrectDataPacket[s.lastSent, s.lastReceived] or s'.pipe = generateCorrectDataPacket[s.lastSent, s.lastReceived]) and s'.lastSent = s.lastSent
	else s'.status[Sender]=Acking and s'.pipe = s.pipe and s'.lastSent = s.lastSent

	(s.pipe not = none) and (s.pipe.data in Data - Ack) => s'.status[Receiver] = Receiving
	else s'.status[Receiver] = Waiting
}

pred takePacketFromPipeSendAckTransition[s,s' : SystemState]{
	s'.status[Sender] = Acking
	s'.status[Receiver] = Waiting
	s'.lastSent = s.lastSent
	s'.lastSentSequence = s.lastSentSequence
	s'.buffers[Sender] = s.buffers[Sender]
	s.pipe.checksum = Global.checksums[s.pipe.data] => s'.buffers[Receiver] = s.buffers[Receiver] + s.pipe.data and (s'.pipe = generateCorrectDataPacket[Ack, s.getNextNumber[]] or s'.pipe = generateIncorrectDataPacket[Ack, s.getNextNumber[]]) and s'.lastReceived = s.getNextNumber[]
	else s'.buffers[Receiver] = s.buffers[Receiver] and (s'.pipe = generateCorrectDataPacket[Ack, s.lastReceived] or s'.pipe = generateIncorrectDataPacket[Ack, s.lastReceived]) and s'.lastReceived = s.lastReceived
	
	s'.pipe not = none
}

fact States {
	no s: SystemState | s.status[s.receiver] = Sending or s.status[s.receiver] = Acking or s.status[s.sender] = Receiving
	all s: SystemState | #(s.status[s.receiver]) = 1 and #(s.status[s.sender]) = 1
}

pred Trace {
	first.Init[]
	all s : SystemState - last | Transition[s, s.next]
}

pred TraceWithCorruptedAck {
	first.InitCorruptAck[]
	all s : SystemState - last | Transition[s, s.next]
}

pred sendAll {
	Trace and some s: SystemState | (no d: Data - Ack | d in s.buffers[s.sender]) and (all d: Data - Ack | d in s.buffers[Receiver] and s.status[Sender] = Waiting and s.status[Receiver] = Waiting)
}

//With no Errors
run sendAll for 6 but exactly 2 Data, exactly 3 Packet
//With 1 Error
run sendAll for 9 but exactly 2 Data, exactly 4 Packet
//With 2 Errors
run sendAll for 12 but exactly 2 Data, exactly 4 Packet

assert sendWithCorruptAck {
	TraceWithCorruptedAck=> (no p: Packet | p in last.pipe) and (all d: Data - Ack | d in last.buffers[last.receiver]) and (last.status[Sender] = Waiting and last.status[Receiver] = Waiting)
}

check sendWithCorruptAck for 12 but exactly 3 Data, exactly 4 Packet

assert alwaysSends {
	Trace => (no d: Data - Ack | d in last.buffers[Sender]) and (all d: Data - Ack | d in last.buffers[Receiver] and last.status[Sender] = Waiting and last.status[Receiver] = Waiting)
}

check alwaysSends for 12 but exactly 3 Data, exactly 4 Packet

pred show {
	Trace
}

run show for 6 but exactly 2 Data, exactly 2 Packet
