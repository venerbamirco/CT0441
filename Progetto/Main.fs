(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Main.fs: console e codice main
 *)

module SharpSolver.Main

open Microsoft.FSharp.Text.Lexing
open Absyn
open SharpSolver.Impl
open System
open Prelude
open Microsoft.FSharp.Text


// funzioni di logging e printing
//

let hout hd fmt =
    if not <| String.IsNullOrWhiteSpace hd then
        printf "[%s]%s" hd (new String (' ', max 1 (Config.prefix_max_len - String.length hd)))
        stdout.Flush ()
    printfn fmt

let chout col hd fmt =
    let c = Console.ForegroundColor
    Console.ForegroundColor <- col
    Printf.kprintf (fun s -> hout hd "%s" s; Console.ForegroundColor <- c) fmt

let out fmt = hout "" fmt
let cout col fmt = chout col "" fmt

let norm fmt = chout ConsoleColor.Yellow "norm" fmt
let redux fmt = chout ConsoleColor.Magenta "redux" fmt
let sol fmt = chout ConsoleColor.Green "sol" fmt
let ident fmt = chout ConsoleColor.Green "ident" fmt    
let error fmt = chout ConsoleColor.Red "error" fmt  
//inserito questo per aver un format per il grado
let degree fmt = chout ConsoleColor.Blue "degree" fmt


// interprete dei comandi e delle espressioni
//

let interpreter_loop () =
    while true do
        printf "\n%s" Config.prompt_prefix          // stampa il prompt
        stdout.Flush ()                             // per sicurezza flusha lo stdout per vedere la stampa del prompt senza end-of-line
        let input = Console.ReadLine ()             // leggi l'input scritto dall'utente
        let lexbuf = LexBuffer<_>.FromString input  // crea un lexbuffer sulla stringa di input

        // funzione locale per il pretty-printing degli errori
        let localized_error msg =
            let tabs = new string (' ', Config.prompt_prefix.Length + lexbuf.StartPos.Column)
            let cuts = new string ('^', let n = lexbuf.EndPos.Column - lexbuf.StartPos.Column in if n > 0 then n else 1)
            cout ConsoleColor.Yellow "%s%s\n" tabs cuts
            error "error at %d-%d: %s" lexbuf.StartPos.Column lexbuf.EndPos.Column msg 
        
        // blocco con trapping delle eccezioni
        try
            let line = Parser.line Lexer.tokenize lexbuf    // invoca il parser sul lexbuffer usando il lexer come tokenizzatore
            #if DEBUG
            hout "absyn" "%+A" line
            hout "pretty" "%O" line
            #endif

            // interpreta la linea in base al valore di tipo line prodotto dal parsing
            match line with
            | Cmd "help" ->
                out "%s" Config.help_text

            | Cmd ("quit" | "exit") ->
                out "%s" Config.exit_text
                exit 0

            // TODO: se volete supportare altri comandi, fatelo qui (opzionale)
            
            | Cmd s -> error "unknown command: %s" s    // i comandi non conosciuti cadono in questo caso

            // TODO: aggiungere qui sotto i pattern per i casi Expr ed Equ con relativo codice per, rispettivamente, normalizzare espressioni e risolvere equazioni

            //caso unica espressione senza uguale
            | Expr e1 ->

                //funzione che viene chiamata quando la mia espressione data in input è direttamente un polinomio e quindi non bisogna derivarla
                let poly ( e1 : expr ) ( xs : polynomial ) : unit =
                    //stampo la derivata che nel caso non venga passato la d[] viene stampato direttamente il polinomio dato in input
                    redux "%O"  xs
                    //stampo la normalizzazione
                    norm "%O" ( normalize xs )
                    //stampo il grado
                    degree "%O" ( normalized_polynomial_degree ( normalize xs ) )

                //funzione che viene chiamata quando la mia espressione data in input bisogna derivarla almeno una volta
                let deri ( e1 : expr ) ( xs : expr ) : unit =
                    //stampo la derivata ma prima la calcolo ricorsivamente
                    redux "%O"  ( reduce e1 )
                    //stampo la normalizzazione
                    norm "%O" ( normalize ( reduce e1 ) )
                    //stampo il grado
                    degree "%O" ( normalized_polynomial_degree ( normalize ( reduce e1 ) ) )

                //controllo che dati che contiene e1 se direttamente un polinomio o un espressione da derivare
                match e1 with
                //nel caso quello inserito sia un polinomio
                | Poly xs ->
                    poly e1 xs
                //nel caso quello inserito sia da derivare
                | Derive xs ->
                    deri e1 xs

            //caso uguaglianza con due espressioni
            | Equ (e1, e2) ->

                //funzione che dato un normalized_polynomial mi restituisce una monomial list e la ho fatta per potermi creare la mia equazione e usare il suo metodo tostring
                let rational_to_monomial ( array : normalized_polynomial ) : monomial list =

                    //funzione ausiliare
                    let rec aux ( arr1 : rational [] ) ( lista : monomial list ) ( cont : int ) : monomial list =
                        //se l array è vuoto resituisco la lista
                        if Array.length arr1 = 0 then
                            lista
                        //escludo il primo elemento dell array e lo concateno alla lista e il contatore lo uso come posizione che indica il grado del singolo monomio che viene incrementato di volta in volta
                        else aux ( Array.skip 1 arr1 ) ( lista @ [ Monomial ( arr1.[ 0 ] , cont ) ] ) ( cont + 1 )

                    //fa parte della funzione rational_to_monomial
                    in
                    //estraggo l array di rational
                    match array with
                    | NormalizedPolynomial ( xs ) ->
                        //mi creo il monomial [] e lo inizializzo
                        aux xs [] 0

                //funzione per stampare le soluzioni di un polinomio normalizzato
                let stampa_soluzioni ( norma : normalized_polynomial ) ( grado : int ) : unit =
                    //stampo le soluzioni
                    //caso identità grado 0
                    if grado = 0 then
                        //la risolvo e se vero restituisco soltanto vero perchè uso identità
                        if ( solve0 norma ) then
                            ident "%s" "True" 
                        else 
                            //se no falso perche numero diverso da zero
                            ident "%s" "False" 
                    //1 soluzione grado 1
                    else if grado = 1 then
                        //la risolvo e stampo l eventuale soluzione tramite il format sol
                        sol "%O" ( solve1 norma )
                    //0,1,2 soluzioni grado 2
                    else if grado = 2 then
                        //la risolvo e guardo la quantita di soluzioni per vedere quante soluzioni sono reali e quante immaginarie
                        match solve2 norma with
                        //nel caso ci siano due soluzioni
                        | Some ( x , Some ( y ) ) ->
                            sol "%s" ( "x1 = " + (string) x + " e " + "x2 = " + (string) y )
                        //nel caso ci sia un unica soluzione
                        | Some ( x , None ) ->
                            sol "%s" ( "x1 = " + (string) x + " e " + "x2 = soluzione complessa" )
                        //nel caso non ci sia nessuna soluzione
                        | None ->
                            sol "%s" ( "Nessuna soluzione reale" )
                    else 
                        //nel caso il grado dell equazione e maggiore di 2
                        sol "%s" "Superiore al grado 2" 

                //funzione che racchiude il caso del match poly poly
                let poly_poly ( e1 : expr ) ( e2 : expr ) ( xs : polynomial ) ( ys : polynomial ) : unit =
                    
                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let eq1 = Equ ( e1 , e2 )
                    //stampo la derivata
                    redux "%O" eq1

                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let norma = normalize ( unisci_due_polinomi xs ys )
                    let eq2 = Equ ( Poly ( Polynomial ( rational_to_monomial ( norma ) ) )  , Poly ( Polynomial ( [ Monomial ( rational ( 0 ) , 0 ) ] ) ) )
                    //stampo la normalizzazione
                    norm "%O" eq2
                    
                    //stampo il grado
                    let grado = normalized_polynomial_degree ( normalize ( unisci_due_polinomi xs ys ) )
                    degree "%d" grado

                    //stampo le soluzioni
                    stampa_soluzioni norma grado

                //funzione che racchiude il caso del match poly deri
                let poly_deri ( e1 : expr ) ( e2 : expr ) ( xs : polynomial ) ( ys : polynomial ) : unit =

                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let eq1 = Equ ( e1 , Poly ys )
                    //stampo la derivata
                    redux "%O" eq1

                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let norma = normalize ( unisci_due_polinomi xs ys )
                    let eq2 = Equ ( Poly ( Polynomial ( rational_to_monomial ( norma ) ) )  , Poly ( Polynomial ( [ Monomial ( rational ( 0 ) , 0 ) ] ) ) )
                    //stampo la normalizzazione
                    norm "%O" eq2
                    
                    //stampo il grado
                    let grado = normalized_polynomial_degree ( normalize ( unisci_due_polinomi xs ys ) )
                    degree "%d" grado

                    //stampo le soluzioni
                    stampa_soluzioni norma grado
                    
                
                //funzione che racchiude il caso del match deri poly
                let deri_poly ( e1 : expr ) ( e2 : expr ) ( xs : polynomial ) ( ys : polynomial ) : unit =

                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let eq1 = Equ ( Poly ( xs ) , e2 )
                    //stampo la derivata
                    redux "%O" eq1

                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let norma = normalize ( unisci_due_polinomi xs ys )
                    let eq2 = Equ ( Poly ( Polynomial ( rational_to_monomial ( norma ) ) )  , Poly ( Polynomial ( [ Monomial ( rational ( 0 ) , 0 ) ] ) ) )
                    //stampo la normalizzazione
                    norm "%O" eq2
                    
                    //stampo il grado
                    let grado = normalized_polynomial_degree ( normalize ( unisci_due_polinomi xs ys ) )
                    degree "%d" grado

                    //stampo le soluzioni
                    stampa_soluzioni norma grado
                
                //funzione che racchiude il caso del match poly poly
                let deri_deri ( e1 : expr ) ( e2 : expr ) ( xs : polynomial ) ( ys : polynomial ) : unit =

                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let eq1 = Equ ( Poly ( xs ) , Poly ( ys ) )
                    //stampo la derivata
                    redux "%O" eq1

                    //mi creo l equazione per poter usare il metodo tostring del tipo
                    let norma = normalize ( unisci_due_polinomi xs ys )
                    let eq2 = Equ ( Poly ( Polynomial ( rational_to_monomial ( norma ) ) )  , Poly ( Polynomial ( [ Monomial ( rational ( 0 ) , 0 ) ] ) ) )
                    //stampo la normalizzazione
                    norm "%O" eq2

                    //stampo il grado
                    let grado = normalized_polynomial_degree ( normalize ( unisci_due_polinomi xs ys ) )
                    degree "%d" grado

                    //stampo le soluzioni
                    stampa_soluzioni norma grado

                //controllo che dati contiene e1 e in caso derivo subito le espressioni per evitare operazioni identiche future
                match e1 , e2 with
                //nel caso tutte e due le parti siano polinomi
                | Poly xs, Poly ys -> 
                    poly_poly e1 e2 xs ys
                //nel caso quello di destra sia da derivare e quello di sinistra è un polinomio 
                | Poly xs , Derive ys ->
                    poly_deri e1 e2 xs ( reduce e2 )
                //nel caso quello di destra sia un polinomio e quello di sinistra sia da derivare
                | Derive xs , Poly ys ->
                    deri_poly e1 e2 ( reduce e1 ) ys
                //nel caso da entrambe le parti bisogna derivare
                | Derive xs , Derive ys -> 
                    deri_deri e1 e2 ( reduce e1 ) ( reduce e2 )

            | _ -> raise (NotImplementedException (sprintf "unknown command or expression: %O" line))
                   
        // gestione delle eccezioni
        with LexYacc.ParseErrorContextException ctx ->
                let ctx = ctx :?> Parsing.ParseErrorContext<Parser.token>
                localized_error (sprintf "syntax error%s" (match ctx.CurrentToken with Some t -> sprintf " at token <%O>" t | None -> ""))

           | Lexer.LexerError msg -> localized_error msg 

           | :? NotImplementedException as e -> error "%O" e
        
           | e -> localized_error e.Message


// funzione main: il programma comincia da qui
//

[<EntryPoint>]
let main _ = 
    let code =
        try
            interpreter_loop ()                 // chiama l'interprete
            0                                   // ritorna il codice di errore 0 (nessun errore) al sistema operativo se tutto è andato liscio
        with e -> error "fatal error: %O" e; 1  // in caso di eccezione esce con codice di errore 1
    #if DEBUG
    Console.ReadKey () |> ignore                // aspetta la pressione di un tasto prima di chiudere la finestra del terminare 
    #endif
    code


