abstract sig Vehicle {
    location: one Location
}
sig PassengerVehicle extends Vehicle {
    seats: one Int,
    passengers: set Person
}
sig CargoVehicle extends Vehicle {
    capacity: one Int,
}

abstract sig Material {
    Quantity: one Int
}
sig Lumber extends Material {}
sig Concrete extends Material {}
sig Steel extends Material {}

pred isSubtypeOf[m1, m2: Material] {
    (m1 in Lumber and m2 in Lumber) or
    (m1 in Concrete and m2 in Concrete) or
    (m1 in Steel and m2 in Steel)
}

abstract sig Location {
    job: lone Job,
    vehicles: set Vehicle,
    materials: set Material
}
sig Residence extends Location {}
sig Workplace extends Location {
    //job: one Job
}
sig Warehouse extends Location {}

sig Job{
    requiredMaterials: set Material,
    requiredRoles: set Role
}

abstract sig Person{
    role: one Role,
    location: one Location
}

abstract sig Role {}
sig Manager extends Role {}
sig Architect extends Role {}
sig ConstructionWorker extends Role {}

fact {
    // The number of passengers in a vehicle cannot be more than the number of available seats
    all pv: PassengerVehicle | #pv.passengers <= pv.seats
    // Passenger vehicles must have at least two seats
    all pv: PassengerVehicle| pv.seats >= 2
    // Cargo Vehicles must have at least 3 capacity
    all cv: CargoVehicle | cv.capacity >= 3
}

fact {
    // A job must require a non-negative number of people
    all j: Job | some j.requiredRoles
}
fact {
    // Every person must only be in one location at a time
    all p: Person | one p.location
}
fact{//All roles must be assigned to one person
    all r: Role | one p: Person | p.role = r
}
fact {
    //All materials must be greater than 0
    all m: Material | m.Quantity > 0
    // There cannot be more than one type of Material subclass in one collection
    //all mc: set Material| all m1, m2: mc | m1.isSubtypeOf[m2]
}
fact {//All materials must either be in a vehicle or at a location
    all m: Material | m in Location.materials or m in Job.requiredMaterials
}
fact {
    //Jobs must be in a location
    all j: Job | j in Location.job
    // No shared jobs between locations
    and all x, y : Location | no (x.job & y.job)
}
fact {
    // Each vehicle is in one place at a time
    all disj x,y : Location | no (x.vehicles & y.vehicles)
    all l:Location | l.vehicles.location = l
}
fact {
    // Vehicles cannot have a negative number of seats or loading capacity
    all v: PassengerVehicle | v.seats >= 0
    all v: CargoVehicle | v.capacity >= 0
}

pred movePerson(p:Person,newLoc: Location){
    p.location = newLoc
}

fact {
    // People must move between locations in a vehicle (no walking)
    all v: PassengerVehicle | all p: v.passengers | p.location = v.location
}

pred completeJob(l: Location) {
    let j = l.job |
        // Ensure all required materials are present at workplace
        j.requiredMaterials in {m:Material | m in l.materials}
        // Ensure correct number of people with required roles present
        and all r: j.requiredRoles | some p: Person | p.location = l and p.role = r
}
pred addPassengers[pv: PassengerVehicle] {
    // Get the current location of the PassengerVehicle
    let loc = pv.location |
        // Add all Persons at the same location to the passengers set
        pv.passengers = {p: Person | p.location = loc}
        // Ensure the number of passengers does not exceed the vehicle's capacity
        and #pv.passengers <= pv.seats
}

pred movePassengerVehicle[pv: PassengerVehicle, newLoc: Location] {
    // Ensure the new location is different from the current location
    newLoc != pv.location

    // Add passengers to the vehicle (up to capacity)
    addPassengers[pv]

    // Move the vehicle to the new location
    pv.location = newLoc

    // Move all passengers to the new location
    all p: pv.passengers | movePerson[p, newLoc]
}
// Behavioral items to be added:
pred moveCargoVehicle(cv: one CargoVehicle, to: one Location, materialsToMove: set Material) {
    //Ensure new location is different from current
    to != cv.location
    // Ensure the materials to move are at the current location of the cargo vehicle
    materialsToMove in cv.location.materials
    // Ensure the total quantity of materials to move does not exceed the vehicle's capacity
    let totalQuantity = sum m: materialsToMove | m.Quantity {
        totalQuantity <= cv.capacity
    }
     // Update the vehicle's location
    cv.location = to

    // Remove the materials from the source location
    cv.location.materials = cv.location.materials - materialsToMove

    // Add the materials to the destination location
    to.materials = to.materials + materialsToMove
}


run example{}
run moveCargoVehicle for 10