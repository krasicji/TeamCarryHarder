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
one sig Ack, Nak extends Data {}

sig Checksum {}

fun generateCorrectDataPacket[d: Data, s: Int] : Packet {
	{p: Packet | (p.data = d and p.checksum = Global.checksums[d] and p.sequence = s)}
}

fun generateIncorrectDataPacket[d: Data, s: Int] : Packet {
	{p: Packet | (p.data = d and not p.checksum = Global.checksums[d]  and p.sequence = s)}
}

fun generateResponsePacket[d: Data, s: Int] : Packet {
	{p: Packet | (p.data = d and p.sequence = s)}
}

sig SystemState {
	receiver: Receiver,
	sender: Sender,
	status: Host -> State,
	buffers: Host -> set Data,
	pipe: lone Packet,
	lastSent : lone Data,
	lastRecieved : lone Data,
	currentSequenceNumber: one Int
}

one sig Global {
  checksums: Data one -> one Checksum
}

pred SystemState.Init[] {
	all d: Data - (Ack + Nak)| d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all h: Host | this.status[h] = Waiting
	no this.pipe
	no this.lastSent
	no this.lastRecieved
	this.currentSequenceNumber = 0
	all p: Packet | p.checksum = Global.checksums[p.data] or one p2: Packet | p.data = p2.data and p.checksum not = p2.checksum and p2.checksum = Global.checksums[p.data] and p.data not in Ack + Nak
}

pred SystemState.InitCorruptAckNak[] {
	all d: Data - (Ack + Nak)| d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all h: Host | this.status[h] = Waiting
	no this.pipe
	no this.lastSent
	all p: Packet | p.data not in (Ack+Nak) => (p.checksum = Global.checksums[p.data] or one p2: Packet | p.data = p2.data and p.checksum not = p2.checksum and p2.checksum = Global.checksums[p.data] and p.data not in (Ack + Nak) and (p.sequence = 0 or p.sequence = 1))
	this.currentSequenceNumber = 0
	#{Ack.~data} = 4
	one p: Packet | p.data = Ack and p.sequence = 0 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Ack and p.sequence = 1 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Ack and p.sequence = 0 and p.checksum not = Global.checksums[p.data]
	one p: Packet | p.data = Ack and p.sequence = 1 and p.checksum not = Global.checksums[p.data]
	#{Nak.~data} = 4
	one p: Packet | p.data = Nak and p.sequence = 0 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Nak and p.sequence = 1 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Nak and p.sequence = 0 and p.checksum not = Global.checksums[p.data]
	one p: Packet | p.data = Nak and p.sequence = 1 and p.checksum not = Global.checksums[p.data]
}

pred SystemState.InitCorruptAckNakOnly[] {
	all d: Data - (Ack + Nak)| d in this.buffers[this.sender] and d not in this.buffers[this.receiver]
	all h: Host | this.status[h] = Waiting
	no this.pipe
	no this.lastSent
	all p: Packet | p.data not in (Ack+Nak) => p.checksum = Global.checksums[p.data]
	this.currentSequenceNumber = 0
	#{Ack.~data} = 4
	one p: Packet | p.data = Ack and p.sequence = 0 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Ack and p.sequence = 1 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Ack and p.sequence = 0 and p.checksum not = Global.checksums[p.data]
	one p: Packet | p.data = Ack and p.sequence = 1 and p.checksum not = Global.checksums[p.data]
	#{Nak.~data} = 4
	one p: Packet | p.data = Nak and p.sequence = 0 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Nak and p.sequence = 1 and p.checksum = Global.checksums[p.data]
	one p: Packet | p.data = Nak and p.sequence = 0 and p.checksum not = Global.checksums[p.data]
	one p: Packet | p.data = Nak and p.sequence = 1 and p.checksum not = Global.checksums[p.data]
}

pred Transition[s, s' : SystemState] {
	s.status[Sender] = Waiting and s.status[Receiver] = Waiting => bothWaitingTransition[s,s']
	else s.status[Sender] = Sending and s.status[Receiver] = Waiting => sendPacketIntoPipeTransition[s,s']
	else s.status[Sender] = Acking and s.status[Receiver] = Waiting => switchToReceivingTransition[s,s']
	else s.status[Sender] = Acking and s.status[Receiver] = Receiving => takePacketFromPipeSendAckTransition[s,s']
}

fact {
	no d: Ack + Nak | d in SystemState.buffers[Host]
	all p:Packet | (p.sequence = 0 or p.sequence = 1)
	all s:SystemState | (s.currentSequenceNumber = 0 or s.currentSequenceNumber = 1)
}

pred bothWaitingTransition[s,s' : SystemState] {
	s'.pipe = s.pipe
	s'.buffers = s.buffers
	s'.lastSent = s.lastSent
	s'.lastRecieved = s.lastRecieved
	s'.currentSequenceNumber = s.currentSequenceNumber

	(some s.buffers[Sender]) => s'.status[Sender] = Sending
	else s'.status[Sender] = Waiting

	(s.pipe not = none) and (s.pipe.data in Data - Ack - Nak) => s'.status[Receiver] = Receiving
	else s'.status[Receiver] = Waiting

	//Force the exact number of states to generate an instance
	s.pipe = none and s.buffers[Sender] = none => 1 = 0
}

pred sendPacketIntoPipeTransition[s,s' : SystemState] {
	s'.status[Sender] = Acking
	s'.status[Receiver] = Waiting
	s'.buffers[Receiver] = s.buffers[Receiver]
	s'.lastRecieved = s.lastRecieved
	s'.currentSequenceNumber = s.currentSequenceNumber

	(one d: s.buffers[Sender] | (s'.pipe = generateIncorrectDataPacket[d, s'.currentSequenceNumber] or s'.pipe = generateCorrectDataPacket[d, s'.currentSequenceNumber]) and s'.pipe not = none and s'.buffers[Sender] = s.buffers[Sender] - d and s'.lastSent = d)
}

pred  switchToReceivingTransition[s,s' : SystemState]{
	s'.buffers = s.buffers
	s'.lastRecieved = s.lastRecieved
	((s.pipe not = none) and s.pipe.data = Ack and s.pipe.checksum = Global.checksums[s.pipe.data]) => (s'.status[Sender] = Waiting and (no s'.pipe) and (no s'.lastSent) and (s.currentSequenceNumber = 1 => s'.currentSequenceNumber= 0) and (s.currentSequenceNumber= 0 => s'.currentSequenceNumber = 1))
	else ((s.pipe not = none) and s.pipe.data = Ack and s.pipe.checksum not = Global.checksums[s.pipe.data])  =>  (s'.status[Sender]=Acking and (s'.pipe = generateCorrectDataPacket[s.lastSent, s.currentSequenceNumber] or s'.pipe = generateIncorrectDataPacket[s.lastSent, s.currentSequenceNumber]) and s'.pipe not = none and s'.lastSent = s.lastSent and s'.currentSequenceNumber = s.currentSequenceNumber)
	else ((s.pipe not = none) and s.pipe.data = Nak )=> (s'.status[Sender] = Acking and (s'.pipe = generateIncorrectDataPacket[s.lastSent, s'.currentSequenceNumber] or s'.pipe = generateCorrectDataPacket[s.lastSent, s'.currentSequenceNumber]) and s'.lastSent = s.lastSent and  s'.currentSequenceNumber = s.currentSequenceNumber)
	else (s'.status[Sender]=Acking and s'.pipe = s.pipe and s'.lastSent = s.lastSent and s'.currentSequenceNumber = s.currentSequenceNumber)

	(s.pipe not = none) and (s.pipe.data in Data - Ack - Nak) => s'.status[Receiver] = Receiving
	else s'.status[Receiver] = Waiting
}

pred takePacketFromPipeSendAckTransition[s,s' : SystemState]{
	s'.status[Sender] = Acking
	s'.status[Receiver] = Waiting
	s'.lastSent = s.lastSent
	s'.currentSequenceNumber = s.currentSequenceNumber

	s'.buffers[Sender] = s.buffers[Sender]
	(s.pipe.data not = s.lastRecieved and s.pipe.checksum = Global.checksums[s.pipe.data]) => s'.buffers[Receiver] = s.buffers[Receiver] + s.pipe.data and s'.lastRecieved = s.pipe.data and (s'.pipe = generateCorrectDataPacket[Ack, s'.currentSequenceNumber] or s'.pipe = generateIncorrectDataPacket[Ack, s'.currentSequenceNumber])
	else (s.pipe.data = s.lastRecieved and s.pipe.checksum = Global.checksums[s.pipe.data]) => s'.buffers[Receiver] = s.buffers[Receiver] and s'.lastRecieved = s.lastRecieved and (s'.pipe = generateCorrectDataPacket[Ack, s'.currentSequenceNumber] or s'.pipe = generateIncorrectDataPacket[Ack, s'.currentSequenceNumber])
	else s'.buffers[Receiver] = s.buffers[Receiver] and (s'.pipe = generateCorrectDataPacket[Nak, s'.currentSequenceNumber] or s'.pipe = generateIncorrectDataPacket[Nak, s'.currentSequenceNumber]) and s'.lastRecieved = s.lastRecieved
	
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

pred TraceWithCorruptedAckOrNak {
	first.InitCorruptAckNak[]
	all s : SystemState - last | Transition[s, s.next]
}

pred sendAll {
	Trace and some s: SystemState | (no d: Data - Ack - Nak| d in s.buffers[s.sender]) and (all d: Data - Ack - Nak | d in s.buffers[Receiver] and s.status[Sender] = Waiting and s.status[Receiver] = Waiting)
}

//With no Errors
run sendAll for 6 but exactly 3 Data, exactly 4 Packet
//With 1 Error
run sendAll for 9 but exactly 3 Data, exactly 4 Packet
//With 2 Errors
run sendAll for 12 but exactly 3 Data, exactly 4 Packet

pred sendWithCorruptAckOrNak {
	TraceWithCorruptedAckOrNak and some s: SystemState | (no d: Data - Ack - Nak| d in s.buffers[s.sender]) and (all d: Data - Ack - Nak | d in s.buffers[Receiver] and s.status[Sender] = Waiting and s.status[Receiver] = Waiting)
}

run sendWithCorruptAckOrNak for 9 but exactly 3 Data, exactly 10 Packet

assert alwaysSends {
	Trace => (no d: Data - Ack - Nak| d in last.buffers[Sender]) and (all d: Data - Ack - Nak | d in last.buffers[Receiver] and last.status[Sender] = Waiting and last.status[Receiver] = Waiting)
}

check alwaysSends for 12 but exactly 3 Data, exactly 4 Packet
