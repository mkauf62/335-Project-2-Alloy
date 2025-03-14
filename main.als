abstract sig Vehicle {}
sig PassengerVehicle extends Vehicle {
    seats: one Int
    passengers: set Person
}
sig CargoVehicle extends Vehicle {
    capacity: one Int
    carriedMaterials: set Material
}

abstract sig Material {
    Quantity: one Int
}
sig Lumber extends Material {}
sig Concrete extends Material {}
sig Steel extends Material {}

sig Materials {
    collection: set Material
}

abstract sig Location {
    job: lone Job,
    vehicles: set Vehicle
}
sig Residence extends Location {}
sig Workplace extends Location {
    job: one Job
}
sig Warehouse extends Location {}

sig Job{
    requiredMaterials: Materials,
    requiredRoles: Role -> Int
}

abstract sig People{
    role: one Role
    location: one Location
}

abstract sig Role {}
sig Manager extends Role {}
sig Architect extends Role {}
sig ConstructionWorker extends Role {}

fact {
    // The number of passengers in a vehicle cannot be more than the number of available seats
    all pv: PassengerVehicle | #pv.passengers <= pv.seats
    // The total amount of material being carried cannot exceed the Cargo Vehicles capacity
    all cv: CargoVehicle | sum t: cv.carriedMaterials | t.Quantity <= cv.capacity
}

fact {
    // A job must require a non-negative number of people
    all j: Job | j.requiredPeople >= 0
}
fact {
    // Every person must only be in one location at a time
    all p: Person | one p.location
}

fact {
    //All materials must be greater than or equal to 0
    all m: Material | m.Quantity >= 0
}
fact {
  // Jobs must be unique to locations
  all disj x, y : Location | no (x.job & y.job)
}
fact {
  // Jobs must be unique to locations
  all disj x, y : Job | no (x.Required & y.Required)
}
fact {
    // Each vehicle is in one place at a time
    all disj x,y : Location | no (x.vehicles & y.vehicles)
}
fact {
    // Vehicles cannot have a negative number of seats or loading capacity
    all v: PassengerVehicle | v.seats >= 0
    all v: CargoVehicle | v.capacity >= 0
}

pred moveVehicle(v: Vehicle, from: Location, to: Location) {
    v in from.vehicles
    v not in to.vehicles
    v' in to.vehicles
}

fact {
    // People must move between locations in a vehicle (no walking)
    all p: Person | some pv: PassengerVehicle | p in pv.passengers => p.location = pv.location
}

pred completeJob(w: Workplace) {
    let j = w.job |
        // Ensure all required materials are present at workplace
        j.requiredMaterials.collection in {m:Material | m in w}
        // Ensure correct number of people with required roles present
        and all r: Role |
            (some j.requiredRoles[r]) implies
            (# {p: Person | p.location = w and p.role = r} >= j.requiredRoles[r])
}

// Behavioral items to be added:

// Should update to ensure that people do not overload Passenger Vehicles & can only move by vehicle
pred movePerson(p: Person, from: Location, to: Location) {
    p.location = from
    p.location = to
}

pred moveCargoVehicle(cv: CargoVehicle, from: Location, to: Location) {
    // Ensure all carried materials move with cargo vehicle
}

pred completeJob(w: Workplace) {
    // Remove job from workplace or mark as complete so it's ignored in future evaluations
}

pred loadMaterials(cv: CargoVehicle, loc: location, materials: set Material) {
    // Ensure materials can only be loaded if they exist at the cv location & that the cv cannot be overloaded
}

pred unloadMaterials(cv: CargoVehicle, loc: Location, materials: set Material) {
    // Ensure materials are removed from vehicle when unloaded & place materials at new location i.e. workplace
}

run example{}