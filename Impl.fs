
(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Impl

open Absyn
open Prelude
open System

//funzione che dato un numero con la virgola lo trasforma in un numero senza virgola e diviso per potenza di dieci
let rationalize ( x : float ) : rational = 
    //ho usato questo modo per risolvere problemi di arrotondamento nei casi 7.343 e 0.235999
    //estraggo la lunghezza del float
    let cont = float ( x.ToString().Length )
    //creo il numeratore
    let num = ( int ) ( x * 10.0 ** cont )
    //creo il denominatore
    let den = ( int ) ( 10.0 ** cont )
    //creo il rational e lo restituisco
    rational ( num , den )
    
//funzione che mi restituisce il grado del monomio
let monomial_degree ( m : monomial ) : int = 
    //serve per estrarre la coppia coefficiente grado
    match m with
    | Monomial ( coefficiente , grado ) -> grado

//funzione che nega il coefficiente
let monomial_negate ( m : monomial ) : monomial = 
    match m with
    //serve per estrarre la coppia coefficiente grado
    | Monomial ( coefficiente , grado ) -> 
        //restituisco il coeffiente negato
        Monomial ( - coefficiente , grado )

//funzione che restituisce il grado del polinomio
let polynomial_degree ( p : polynomial ) : int = 

    //funzione ausiliaria
    let aux ( p : polynomial ) ( acc : int ) : int =

        //funzione che data una lista di monomial mi resituisce il grado piu alto
        let rec grado_maggiore ( lista : monomial list ) ( gradomax : int ) : int =
            //scorro la lista
            match lista with
            //restituisco il grado maggiore
            | [] -> gradomax
            //guardo se quelli successivi sono piu grandi
            | x :: xs ->
                //se il grado del monomio è maggiore di quello memorizzato allora lo assegno
                if monomial_degree x > gradomax then
                    grado_maggiore xs ( monomial_degree x )
                //oppure passo quello già memorizzato perche maggiore
                else grado_maggiore xs gradomax

        //fa parte della funzione aux
        in
        match p with
        //estraggo la lista di monomi che compongono polynomial
        | Polynomial ( xs ) -> 
            //calcolo il grado piu elevato tra tutti i monomi
            grado_maggiore xs 0

    //fa parte della funzione polynomial_degree
    in 
    aux p 0

//funzione che restituisce il polinomio negato
let polynomial_negate ( p : polynomial ) : polynomial = 

    //funzione per negare coefficienti lista monomial
    let rec nega_coefficienti ( lista : monomial list ) ( acc : monomial list ) : monomial list =
        //scorro la lista
        match lista with
        //restituisco la lista di monomi negata
        | [] -> acc
        //vado a negare i monomi successivi
        | x :: xs ->
            match x with
            //estraggo il coefficiente da monomial
            | Monomial ( coefficiente , grado ) ->
                //uso un parametro accumulatore per concatenare il singolo monomio negato
                nega_coefficienti xs ( acc @ [ Monomial ( - coefficiente , grado ) ] )

    //fa parte della funzione polynomial_negate
    in
    //estraggo la lista di monomial che compongono polinomial
    match p with
    | Polynomial ( xs ) ->
        //trasformo il monomial list in polinomial
        Polynomial ( nega_coefficienti xs [] )

//prende un polinomio normalizzato e restituisce il suo grado
let normalized_polynomial_degree (np : normalized_polynomial) : int = 
    //estraggo l array di rational che lo compone
    match np with
    | NormalizedPolynomial ( xs ) ->
        //dato che è normalizzato quindi non ci sono monomi simili, allora il grado è la lunghezza meno 1
        Array.length xs - 1
    
//funzione che mi normalizza un polinomio
let normalize ( p : polynomial ) : normalized_polynomial = 

    //funzione che data una lista di monomi somma quelli simili
    let rec calcola_monomi_simili ( lista : monomial list ) ( acc : rational [] ) : rational [] =

        //funzione che mi restituisce la lista dopo aver inserito il coefficiente del monomio in posizione del grado
        let inserisci ( coefficiente : rational ) ( posizione : int ) ( array : rational [] ) : rational [] =
            //sommo il valore nuovo al valore precedente
            array.[ posizione ] <- array.[ posizione ] + coefficiente
            array

        //fa parte della funzione calcola_monomi_simili
        in
        //scorro la lista
        match lista with
        //restituisco il polinomio normalizzato dopo aver sommato tutti i monomi simili
        | [] -> acc
        //guardo se ci sono altri monomi simili
        | x :: xs ->
            //estraggo il singolo monomio come coppia coefficiente grado
            match x with
            | Monomial ( coefficiente , grado ) ->
                //richiamo la funzione subito dopo aver sommato nella giusta posizione della lista il singolo monomio selezionato
                calcola_monomi_simili xs ( inserisci coefficiente grado acc )
                
    //fa parte della funzione normalize
    in
    //estraggo la lista di monomi
    match p with
    | Polynomial ( xs ) ->
        //determino la lunghezza della lista di monomi
        let lunghezzapol = polynomial_degree ( Polynomial ( xs ) )
        //creo array di n posizioni
        let array = Array.init ( lunghezzapol + 1 ) ( fun _ -> rational ( 0 , 1 ) )
        //restituisco il polinomio normalizzato
        NormalizedPolynomial ( calcola_monomi_simili xs array )
       
//funzione che deriva un polinomio
let derive (p : polynomial) : polynomial =

    //funzione per derivare singolo monomio
    let deriva_singolo_monomio ( monomio : monomial ) : monomial =
        //estraggo coefficiente e grado
        match monomio with
        | Monomial ( coefficiente , grado ) ->
            //se il grado è uguale a 0
            if grado = 0 then Monomial ( rational ( 0 , 1 ) , 0 )
            //uso la formula di derivazione di un polinomio n*ax^(n-1)
            else
            Monomial ( ( rational ( grado ) ) * coefficiente , grado - 1 )

    //funzione ausiliare
    let rec aux ( lista : monomial list ) ( acc  : monomial list ) : monomial list =
        //scorro la lista
        match lista with
        //restituisco la lista di monomi derivati
        | [] -> acc
        //derivo anche i monomi seguenti
        | x :: xs ->
            //controllo il risultato della derivazione e lo concateno alla lista solo se diverso da 0
            //e questo perche la derivata di un termine noto e 0
            if deriva_singolo_monomio x = Monomial ( rational ( 0 , 1 ) , 0 ) then
                aux xs acc
            else aux xs ( acc @ [ deriva_singolo_monomio x ] )

    //fa parte della funzione derive
    in
    match p with
    //estraggo la lista di monomi
    | Polynomial ( xs ) ->
        //calcolo la derivata della lista di monomi appena ottenuti
        Polynomial ( aux xs [] )

//funzione che riduce l espressione nel caso questa sia composta da piu derivazioni o altro
let reduce (e : expr) : polynomial = 

    //fnzione ausiliare per poter derivare piu volte ricorsivamente
    let rec aux (e : expr) : polynomial =
        //estraggo le informazioni dall espressione e
        match e with
        //nel caso quello inserito sia un polinomio
        | Poly xs -> xs
        //nel caso quello inserito sia da derivare richiamo derive ricorsivamente
        | Derive xs -> 
            derive ( aux xs )

    //fa parte della funzione reduce
    in
    aux e

//funzione per unire le due parti di un uguaglianza
let unisci_due_polinomi ( p1 : polynomial ) ( p2 :polynomial ) : polynomial =

    //funzione ausiliaria
    let rec aux ( p1 : monomial list ) ( p2 : monomial list ) ( acc : monomial list ) : monomial list =
        match p1 , p2 with
        //se sono nulli entrambi restituisco accumulatore
        | [] , [] -> acc
        //se una nulla resituisco l accumulatore piu l altra lista
        | [] , _ -> 
            //devo invertire i segni del secondo polinomio 
            //estrapolo la lista di monomi
            match ( polynomial_negate ( Polynomial ( p2 ) ) ) with
            | Polynomial ( xs ) -> acc @ xs
        | _ , [] -> acc @ p1
        //se tutte e due valide concateno il primo elemento della prima lista
        | x :: xs , y :: ys ->
            aux xs p2 ( acc @ [ x ] )

    //fa parte della funzione unisci_due_polinomi
    in
    match p1 , p2 with
    //estrapolo dai due polinomi le loro liste di monomi e poi le passo alla funzione per concatenarle
    | Polynomial ( xs ) , Polynomial ( ys ) ->
        //concateno le due liste di monomi appena ottenuti
        Polynomial ( aux xs ys [] )   

//funzione per risolvere equazioni di grado 0 tramite identita se uguali a 0
let solve0 (np : normalized_polynomial) : bool = 
    //estraggo l array di rational che lo compone
    match np with
    | NormalizedPolynomial ( xs ) ->
        //se il termine noto è uguale a 0 restituisco vero se no falso
        if xs.[0] = rational ( 0 ) then true
        else false

//funzione per risolvere equazioni di grado 1 
let solve1 (np : normalized_polynomial) : rational = 
    //estraggo l array di rational che lo compone
    match np with
    | NormalizedPolynomial ( xs ) ->
        //uso la formula da ax + b = 0 -> x = - b / a
        - xs.[ 0 ] / xs.[ 1 ]

//funzione per risolvere equazioni di grado 2
let solve2 (np : normalized_polynomial) : (float * float option) option = 
    //estraggo l array di rational che lo compone
    match np with
    | NormalizedPolynomial ( xs ) ->
        //uso la formula da ax^2 + bx + c = 0 e uso la classica formula
        //memorizzo il delta
        let delta = xs.[ 1 ] ** 2 - rational ( 4 ) * xs.[ 2 ] * xs.[ 0 ]
        //controllo il delta
        //se positivo doppia soluzione
        if delta > rational ( 0 ) then
            //calcolo tutti i parametri della formula risolutiva e li converto in float dato il tipo restituito della funzione
            let menob = ( float ) ( - xs.[ 1 ] )
            let ballaseconda = ( float ) ( xs.[ 1 ] * xs.[ 1 ] )
            let quattroac = ( float ) ( rational ( 4 ) * xs.[ 2 ] * xs.[ 0 ] )
            let duea = ( float ) ( rational ( 2 ) * xs.[ 2 ] )
            //memorizzo le due soluzioni
            let sol1 = ( menob - sqrt ( ballaseconda - quattroac ) ) / duea
            let sol2 = ( menob + sqrt ( ballaseconda - quattroac ) ) / duea
            Some ( sol1 , Some ( sol2 ) )
        //se uguale a zero due soluzioni coincidenti
        else if delta = rational ( 0 ) then
            //calcolo tutti i parametri della formula risolutiva e li converto in float dato il tipo restituito della funzione
            let menob = ( float ) ( - xs.[ 1 ] )
            let ballaseconda = ( float ) ( xs.[ 1 ] * xs.[ 1 ] )
            let quattroac = ( float ) ( rational ( 4 ) * xs.[ 2 ] * xs.[ 0 ] )
            let duea = ( float ) ( rational ( 2 ) * xs.[ 2 ] )
            //memorizzo le due soluzioni
            let sol1 = ( menob - sqrt ( ballaseconda - quattroac ) ) / duea
            Some ( sol1 , None )
        //se minore di 0 nessuna sluzione reale
        else
            None




