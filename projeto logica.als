module sistemaDeIrrigacao

sig MaquinaDeIrrigacao {
	tanque: one TanqueDeAgua,
	bateria: one Bateria
}

sig Sensor {

}

abstract sig Base {	}

sig BaseDeEnergia extends Base { }

sig BaseDeAgua extends Base { }

sig Bateria {
	celulas: set Celula
}

sig Celula { }

sig TanqueDeAgua { }

pred bateriaPorMaquina[b:Bateria] {
	one b.~bateria
}

pred tanquePorMaquina[t:TanqueDeAgua] {
	one t.~tanque
}

pred celulaPorBateria[c:Celula] {
	one 	c.~celulas
}

fun conjuntoDeCelulas[b:Bateria]: set Celula {
	b.celulas
}

fact invariantes {
	
	#MaquinaDeIrrigacao = 4
	#Sensor = 5
	#BaseDeEnergia = 1
	#BaseDeAgua = 1

	all b:Bateria | bateriaPorMaquina[b]

	all t:TanqueDeAgua| tanquePorMaquina[t]

	all c:Celula | celulaPorBateria[c]

	all b:Bateria | #(conjuntoDeCelulas[b]) = 3
}

pred show[]  {}

run show for 12
