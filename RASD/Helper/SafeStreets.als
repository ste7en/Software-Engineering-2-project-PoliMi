// SIGNATURES

abstract sig RegisteredEntity {
	visibilityLevel: one Int
} {visibilityLevel = 0 or visibilityLevel = 1}

sig Individual { }
sig Email { }

sig User extends RegisteredEntity {
	individual: one Individual,
	email: one Email
} { visibilityLevel = 0 }

sig Municipality extends RegisteredEntity {
	referenceCode: one Int
} { visibilityLevel = 1 and referenceCode > 0 }

sig Metadata { }
sig Picture {
	width: one Int,
	height: one Int,
	data: one Metadata
} { width > 0 and height > 0}

sig Position {
	latitude: one Int,
	longitude: one Int
} { latitude > 0 and longitude > 0 }

// Fields describing the type of violation and
// the license plate number have been, for simplicity
// reasons, modeled as integers instead of strings
sig UserReport {
	timestamp: one Int,
	typeOfViolation: one Int,
	licensePlateNumber: one Int,
	picture: one Picture,
	position: one Position
} { licensePlateNumber > 0 and timestamp > 0 }

one sig SafeStreets {
	registeredUsers: set User,
	registeredMunicipalities: set Municipality,
	violationReports: UserReport -> one User
}

// FUNCTIONS

// FACT
fact uniqueEmailForUsers {
	all e: Email | one u: User | u.email = e
}
fact uniqueRefCodeForMunicipalities {
	all m1, m2: Municipality | (m1 != m2 iff m1.referenceCode != m2.referenceCode)
}
fact allUsersBelongToSafeStreets {
	all u: User | u in SafeStreets.registeredUsers
}
fact allMunicipalitiesBelongToSafeStreets {
	all m: Municipality | m in SafeStreets.registeredMunicipalities
}
fact userIndividualIsUnique {
	all i: Individual | one u: User | u.individual = i
}
fact pictureBelongsToOneReport {
	all p: Picture | some r: UserReport | r.picture = p
}
fact positionBelongsToReport {
	all p: Position | some r: UserReport | r.position = p
}
fact metadataBelongsToOnePicture {
	all m: Metadata | some p: Picture | p.data = m
}
fact allUserReportsBelongToSafeStreets {
	all r: UserReport | some u: User | r -> u in SafeStreets.violationReports
}


// PREDICATES

pred show{}

// ASSERTIONS


// CHECKS 

// RUN
run show for 20
