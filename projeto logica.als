module sistemaDeIrrigacao

open util/ordering[Time] as to

------------------------------------------------------------- Assinaturas -------------------------------------------------------------

sig Time { }

sig MaquinaDeIrrigacao {
	tanque: one TanqueDeAgua,
	bateria: one Bateria
}

sig Sensor {
	maquinaNoSensor: MaquinaDeIrrigacao -> Time
}

abstract sig Base { 
	maquinaNaBase: MaquinaDeIrrigacao -> Time
}

sig BaseDeEnergia extends Base { }

sig BaseDeAgua extends Base { }

sig Bateria {
	celulas: Celula -> Time
}

sig Celula {}

sig TanqueDeAgua { }

------------------------------------------------------------- Predicados -------------------------------------------------------------

-- Restringe que cada máquina possui apenas um tanque de água, independente do tempo.
pred umTanquePorMaquina[m: MaquinaDeIrrigacao] {
	one m.tanque
}

-- Restringe que cada tanque pertence à uma única máquina, independente do tempo.
pred tanqueApenasEmUmaMaquina[t:TanqueDeAgua] {
	one t.~tanque
}

-- Restringe que cada máquina possui apenas um bateria, independente do tempo.
pred umaBateriaPorMaquina[m: MaquinaDeIrrigacao] {
	one m.bateria
}

-- Restringe que cada bateria pertence à uma única máquina, independente do tempo.
pred bateriaApenasEmUmaMaquina[b:Bateria] {
	one b.~bateria
}

-- Restringe que cada bateria possui, no máximo, três células, em um determinado tempo.
pred maximoDeCelulasPorBateria[b: Bateria, t: Time] {
	#(getCelulas[b, t]) <= 3
}


-- Restringe que cada célula pertence à uma única bateria, em um determinado tempo.
pred celulaApenasEmUmaBateria[c:Celula, t:Time] {
	one c.~(celulas.t)
}

-- Restringe que cada máquina pertence à um único sensor, em um determinado tempo.
pred umSensorPorMaquina[m:MaquinaDeIrrigacao, s1, s2:Sensor, t:Time] {
	s1 in getSensor[m, t] => s2 !in getSensor[m, t]
}

-- Leva uma máquina até o sensor para fazer a irrigação.
pred addMaquinaSensor[m1:MaquinaDeIrrigacao, s:Sensor, t,t':Time,  bAgua:BaseDeAgua, bEnergia:BaseDeEnergia] {
	m1 !in s.maquinaNoSensor.t

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t + m1
}

-- Faz com que a máquina que estava em um sensor, termine a irrigação e vá reabastecer seu tanque e bateria.
pred removeMaquinaSensor[m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia, t,t':Time] {
	m in s.maquinaNoSensor.t

	(s.maquinaNoSensor).t' = (s.maquinaNoSensor).t - m
}

-- Leva uma máquina até a base de água para ter seu tanque reabastecido.
pred addMaquinaBaseDeAgua[m:MaquinaDeIrrigacao, bAgua:BaseDeAgua, s:Sensor, t,t':Time] {
	m !in (bAgua.maquinaNaBase).t
	m in (s.maquinaNoSensor).t

	(bAgua.maquinaNaBase).t' = (bAgua.maquinaNaBase).t + m
}

-- Faz com que a máquina, agora com o tanque cheio, vá reabastecer sua bateria na base de energia.
pred removerDaBaseAgua[m:MaquinaDeIrrigacao,  bAgua:BaseDeAgua, t,t':Time] {
	m in bAgua.maquinaNaBase.t

	bAgua.maquinaNaBase.t' = bAgua.maquinaNaBase.t - m
}

-- Leva uma máquina até a base de energia para ter sua bateria reabastecida, caso necessário.
pred addMaquinaBaseDeEnergia[m:MaquinaDeIrrigacao, bEnergia: BaseDeEnergia, bAgua:BaseDeAgua, t, t':Time] {
	m !in bEnergia.maquinaNaBase.t
	m in bAgua.maquinaNaBase.t

	bEnergia.maquinaNaBase.t' = bEnergia.maquinaNaBase.t + m
}

-- Termina o ciclio da máquina e esta volta ao seu estado inicial.
pred removerDaBaseEnergia[m:MaquinaDeIrrigacao, bEnergia:BaseDeEnergia, t,t':Time] {
	m in bEnergia.maquinaNaBase.t

	bEnergia.maquinaNaBase.t' = bEnergia.maquinaNaBase.t - m
}

-- Restringe que cada sensor possui uma única máquina, em um determinado tempo.
pred umaMaquinaPorSensor[m1, m2:MaquinaDeIrrigacao, s:Sensor, t:Time] {
	m1 in getMaquina[s, t] => m2 !in getMaquina[s, t]
}

-- Restringe que cada máquina pertence à um único sensor, em um determinado tempo.
pred maquinaApenasEmUmSensor[m:MaquinaDeIrrigacao, s1, s2:Sensor, t:Time] {
	s1 in getSensor[m, t] => s2 !in getSensor[m, t]
}

-- Restringe que cada base possui uma única máquina, em um determinado tempo.
pred umaMaquinaPorBase[m1, m2:MaquinaDeIrrigacao, b:Base, t:Time] {
	 m1 in b.maquinaNaBase.t => m2 !in  b.maquinaNaBase.t
}

-- Verifica se uma máquina está em um sensor, em um determinado tempo.
pred estaNoSensor[m:MaquinaDeIrrigacao, s:Sensor, t:Time] {
	m in s.maquinaNoSensor.t
}

-- Verifica se uma máquina está em uma base, em um determinado tempo.
pred estaNaBase[m:MaquinaDeIrrigacao, b:Base, t:Time] {
	m in b.maquinaNaBase.t
}

-- Garante a exclusão mútua dos eventos de atender um sensor, e reabastecer água e bateria em um determinado tempo.
pred umaOperacaoPorVez[m:MaquinaDeIrrigacao, s:Sensor, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia, t:Time] {
	estaNoSensor[m, s, t] => (!estaNaBase[m, bAgua, t]  and !estaNaBase[m, bEnergia, t])
	estaNaBase[m, bAgua, t] => (!estaNoSensor[m, s, t] and !estaNaBase[m, bEnergia, t])
	estaNaBase[m, bEnergia, t]  => (!estaNoSensor[m, s, t] and !estaNaBase[m, bAgua, t] )
}

-- Verifica se a máquina saiu do sensor em um determinado tempo.
pred maquinaSaiuDoSensor[m:MaquinaDeIrrigacao, s:Sensor, t:Time] {
	m in s.maquinaNoSensor.t and  m !in s.maquinaNoSensor.(t.next)
}

-- Verifica se a máquina entrou em uma base em um determinado tempo.
pred maquinaEntrouNaBase[m:MaquinaDeIrrigacao, b:Base, t:Time] {
	m in b.maquinaNaBase.(t.next)
}

-- Verifica se a máquina saiu de uma base em um determinado tempo.
pred maquinaSaiuDaBase[m:MaquinaDeIrrigacao, b:Base, t:Time]{
	m in b.maquinaNaBase.t and m !in b.maquinaNaBase.(t.next)
}

------------------------------------------------------------- Funções -------------------------------------------------------------

-- Retorna o conjunto de células de uma bateria em um determinado tempo.
fun getCelulas[b:Bateria, t:Time]: set Celula {
	b.(celulas.t)
}

-- Retorna a máquina que está ligada ao sensor em um determinado tempo.
fun getMaquina[s:Sensor, t:Time]: one MaquinaDeIrrigacao {
	s.(maquinaNoSensor.t)
}

-- Retorna o sensor que está utilizando a máquina em um determinado tempo.
fun getSensor[m: MaquinaDeIrrigacao, t: Time]: one Sensor {
	m.~(maquinaNoSensor.t)
}

------------------------------------------------------------- Fatos -------------------------------------------------------------

fact quantidades  {

	#MaquinaDeIrrigacao = 4
	#TanqueDeAgua = 4
	#Bateria = 4
	#Celula = 12
	#Sensor = 5
	#BaseDeEnergia = 1
	#BaseDeAgua = 1

}

fact invariantes {

	all m:MaquinaDeIrrigacao | umTanquePorMaquina[m]
	all t:TanqueDeAgua | tanqueApenasEmUmaMaquina[t]
	all m:MaquinaDeIrrigacao | umaBateriaPorMaquina[m]
	all b:Bateria | bateriaApenasEmUmaMaquina[b]
	all c:Celula, t:Time | celulaApenasEmUmaBateria[c, t]
	all b: Bateria, t:Time | maximoDeCelulasPorBateria[b, t]
	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, s1:Sensor, s2:Sensor - s1, t:Time | umaMaquinaPorSensor[m1, m2, s1, t] and maquinaApenasEmUmSensor[m1, s1, s2, t]
	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia | umaOperacaoPorVez[m, s, bAgua, bEnergia, t]
	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, t:Time, b:Base | umaMaquinaPorBase[m1, m2, b, t]

}

fact Sequencial {

	all m:MaquinaDeIrrigacao, s:Sensor, t:Time, bAgua:BaseDeAgua | maquinaSaiuDoSensor[m, s, t] => maquinaEntrouNaBase[m, bAgua, t]
	all m:MaquinaDeIrrigacao, t:Time, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia | maquinaSaiuDaBase[m, bAgua, t] => maquinaEntrouNaBase[m, bEnergia, t]

}

------------------------------------------------------------- Gerenciamento Temporal -------------------------------------------------------------

pred init [t: Time] {
	no (Sensor.maquinaNoSensor).t
	no (BaseDeAgua.maquinaNaBase).t
	no (BaseDeAgua.maquinaNaBase).(t.next)
	no (BaseDeEnergia.maquinaNaBase).t
	no (BaseDeEnergia.maquinaNaBase).(t.next)
	no (BaseDeEnergia.maquinaNaBase).(t.next.next)
	all b:Bateria | #(getCelulas[b, t]) = 3
}

fact traces {
	init [first]
	all pre: Time-last | let pos = pre.next |
	some m1:MaquinaDeIrrigacao, s: Sensor, bAgua:BaseDeAgua, bEnergia:BaseDeEnergia |
		addMaquinaSensor[m1, s, pre, pos, bAgua, bEnergia]  or
		removeMaquinaSensor[m1, s, bAgua, bEnergia, pre, pos] or
		addMaquinaBaseDeAgua[m1, bAgua, s, pre, pos] or
	    removerDaBaseAgua[m1, bAgua, pre, pos] or
		addMaquinaBaseDeEnergia[m1, bEnergia, bAgua, pre, pos] or
		removerDaBaseEnergia[m1, bEnergia, pre, pos]
}

pred show[]  {}

run show for 12

------------------------------------------------------------- Asserts -------------------------------------------------------------

-- Checando se a quantidade das assinaturas no sistema estão corretas.
assert testeQuantidadeDeAssinaturas {
		#MaquinaDeIrrigacao = 4
		#Bateria = 4
		#TanqueDeAgua = 4
		#Sensor = 5
		#BaseDeEnergia = 1
		#BaseDeAgua = 1
}

-- Teste responsável por analisar se toda máquina tem apenas uma bateria e um tanque.
assert testeBateriasTanquePorMaquina {
	all m:MaquinaDeIrrigacao | #(m.bateria) = 1 &&	#(m.tanque) = 1
}

-- Teste responsável por verificar se máquinas não estão compartilhando bateria ou tanque.
assert testeCompartilhamentoDeBateriaOuTanqueNaMaquina {
	all b:Bateria | #(b.~bateria) = 1 
	all t:TanqueDeAgua | #(t.~tanque) = 1
}

-- Verifica se em todo tempo, o número de células por bateria é no maximo 3.
assert testeNumeroDeCelulasPorBaterias {
	all b:Bateria, t:Time | #(getCelulas[b, t]) <= 3
}

-- Verifica se apenas uma máquina pode está na base de água por vez.
assert verificaSeApenasUmaMaquinaNaBaseDeAguaPorTempo {
	all m1:MaquinaDeIrrigacao,m2:MaquinaDeIrrigacao - m1, t:Time, b:Base | m1 in b.maquinaNaBase.t => m2 !in  b.maquinaNaBase.t
}

check testeQuantidadeDeAssinaturas
check testeBateriasTanquePorMaquina 
check testeNumeroDeCelulasPorBaterias
check testeCompartilhamentoDeBateriaOuTanqueNaMaquina
check verificaSeApenasUmaMaquinaNaBaseDeAguaPorTempo
