import csv, math, random, re, statistics, time  # standardní moduly: CSV, matika, náhoda, regex, statistika, čas
import tkinter as tk  # základ grafického okna
from tkinter import ttk, filedialog, messagebox  # moderní prvky, dialog souborů, hlášky

MAX_N, MAX_POMALE, MAX_ANIM = 100_000, 3000, 100  # limity: celkem, pomalé algoritmy, animace
POMALE = {"Bubble sort", "Selection sort", "Insertion sort"}  # algoritmy se složitostí O(n²)


# ===================== ALGORITMY =====================
# Každý algoritmus má běžnou funkci (vrací nové seřazené pole)
# a krokový generátor pro animaci: (pole, aktivní indexy, hotové indexy, popis kroku).

def bubble_sort(data):  # Bubble sort = bublinkové řazení
    a = list(data)  # kopie, aby se vstup nezměnil
    n = len(a)  # počet prvků
    for p in range(n - 1):  # p-tý průchod polem
        prohozeno = False  # zatím jsme nic neprohodili
        for j in range(n - 1 - p):  # posledních p prvků je už hotových
            if a[j] > a[j + 1]:  # sousedé ve špatném pořadí?
                a[j], a[j + 1] = a[j + 1], a[j]  # prohodíme je (ostré >, proto stabilní)
                prohozeno = True  # zapamatujeme si, že se něco změnilo
        if not prohozeno:  # žádná výměna = pole je seřazené
            break  # můžeme skončit dřív
    return a  # vrátíme seřazené pole


def bubble_kroky(data):  # krokový Bubble sort pro animaci
    a = list(data);
    n = len(a)  # kopie pole a jeho délka
    yield list(a), (), set(), "Výchozí pořadí"  # první snímek: nic se neděje
    for p in range(n - 1):  # průchody polem
        prohozeno = False  # příznak výměny
        hotovo = set(range(n - p, n))  # konec pole je už na svém místě
        for j in range(n - 1 - p):  # porovnáváme dvojice sousedů
            if a[j] > a[j + 1]:  # špatné pořadí
                a[j], a[j + 1] = a[j + 1], a[j]  # prohodíme
                prohozeno = True  # něco se změnilo
                popis = f"Pozice {j} a {j + 1}: {a[j + 1]} > {a[j]}, prohazuji"  # text kroku
            else:  # pořadí je správné
                popis = f"Pozice {j} a {j + 1}: {a[j]} ≤ {a[j + 1]}, nechávám"  # text kroku
            yield list(a), (j, j + 1), hotovo, popis  # snímek: dvojice je aktivní (oranžová)
        if not prohozeno:  # nic se neprohodilo
            break  # konec
    yield list(a), (), set(range(n)), "Hotovo"  # závěrečný snímek: vše zelené


def selection_sort(data):  # Selection sort = řazení výběrem
    a = list(data)  # kopie pole
    n = len(a)  # počet prvků
    for i in range(n - 1):  # a[:i] je seřazené, a[i:] ne
        m = i  # index nejmenšího prvku (zatím první)
        for j in range(i + 1, n):  # projdeme zbytek pole
            if a[j] < a[m]:  # našli jsme menší prvek?
                m = j  # zapamatujeme si jeho index
        a[i], a[m] = a[m], a[i]  # minimum dáme na začátek (nestabilní)
    return a  # vrátíme seřazené pole


def selection_kroky(data):  # krokový Selection sort
    a = list(data);
    n = len(a)  # kopie pole a délka
    yield list(a), (), set(), "Výchozí pořadí"  # první snímek
    for i in range(n - 1):  # pozice, kam půjde minimum
        m = i  # zatím nejmenší je první
        for j in range(i + 1, n):  # hledáme minimum v zbytku
            nove = a[j] < a[m]  # je a[j] nové minimum?
            if nove:  # ano
                m = j  # uložíme index
            yield list(a), (m, j), set(range(i)), (  # snímek: minimum a zkoumaný prvek
                    f"Hledám minimum od pozice {i}: pozice {j} ({a[j]}) " +  # text: kde hledáme
                    ("je nové minimum" if nove else "minimum nemění"))  # text: výsledek porovnání
        a[i], a[m] = a[m], a[i]  # výměna minima na pozici i
        yield list(a), (i, m), set(range(i + 1)), f"Minimum {a[i]} dávám na pozici {i}"  # snímek výměny
    yield list(a), (), set(range(n)), "Hotovo"  # závěrečný snímek


def merge_sort(data):  # Merge sort = řazení slučováním
    a = list(data)  # kopie pole
    if len(a) < 2:  # 0 nebo 1 prvek je seřazený
        return a  # není co dělat
    s = len(a) // 2  # střed pole
    L, R = merge_sort(a[:s]), merge_sort(a[s:])  # rozdělit a seřadit obě poloviny
    vysl, i, j = [], 0, 0  # výsledek a ukazatele do L a R
    while i < len(L) and j < len(R):  # dokud mají obě poloviny prvky
        if L[i] <= R[j]:  # při shodě bereme levý (stabilita)
            vysl.append(L[i]);
            i += 1  # vezmeme z levé poloviny
        else:  # pravý prvek je menší
            vysl.append(R[j]);
            j += 1  # vezmeme z pravé poloviny
    return vysl + L[i:] + R[j:]  # zbytek jedné poloviny připojíme


def merge_kroky(data):  # krokový Merge sort
    a = list(data)  # kopie pole
    yield list(a), (), set(), "Výchozí pořadí"  # první snímek
    yield from _merge_rek(a, 0, len(a))  # předáme snímky z rekurze
    yield list(a), (), set(range(len(a))), "Hotovo"  # závěrečný snímek


def _merge_rek(a, lo, hi):  # seřadí úsek a[lo:hi]
    if hi - lo < 2:  # úsek o 0–1 prvku je hotový
        return  # konec rekurze
    s = (lo + hi) // 2  # střed úseku
    yield from _merge_rek(a, lo, s)  # seřadit levou půlku
    yield from _merge_rek(a, s, hi)  # seřadit pravou půlku
    L, R, i, j = a[lo:s], a[s:hi], 0, 0  # kopie půlek a ukazatele
    for k in range(lo, hi):  # plníme pozice k po řadě
        if j >= len(R) or (i < len(L) and L[i] <= R[j]):  # kdy vzít z levé půlky
            a[k] = L[i];
            i += 1  # zapíšeme prvek z levé
        else:  # jinak z pravé
            a[k] = R[j];
            j += 1  # zapíšeme prvek z pravé
        yield (a[:k + 1] + L[i:] + R[j:] + a[hi:], (k,), set(),  # snímek: slité + zbytky půlek
               f"Slévám úsek {lo}–{hi - 1}: na pozici {k} zapisuji {a[k]}")  # text kroku


def quick_sort(data):  # Quick sort = rychlé řazení
    a = list(data)  # kopie pole
    zasobnik = [(0, len(a) - 1)]  # úseky k seřazení (místo rekurze)
    while zasobnik:  # dokud zbývá nějaký úsek
        lo, hi = zasobnik.pop()  # vezmeme poslední úsek
        if lo >= hi:  # prázdný nebo jednoprvkový úsek
            continue  # je hotový
        pivot = a[(lo + hi) // 2]  # pivot = prostřední prvek
        # a[lo:lt] < pivot | a[lt:i] == pivot | a[i:gt+1] neznámé | a[gt+1:] > pivot
        lt, i, gt = lo, lo, hi  # tři ukazatele
        while i <= gt:  # dokud je co zkoumat
            if a[i] < pivot:  # menší než pivot
                a[lt], a[i] = a[i], a[lt]  # pošleme doleva
                lt += 1;
                i += 1  # posuneme oba ukazatele
            elif a[i] > pivot:  # větší než pivot
                a[i], a[gt] = a[gt], a[i]  # pošleme doprava
                gt -= 1  # i neměníme, přišel neznámý prvek
            else:  # rovný pivotu
                i += 1  # zůstane uprostřed
        zasobnik += [(lo, lt - 1), (gt + 1, hi)]  # zbývá levá a pravá část

    return a  # vrátíme seřazené pole


def quick_kroky(data):  # krokový Quick sort
    a = list(data);
    n = len(a);
    hot = set()  # kopie, délka, množina hotových indexů
    yield list(a), (), set(), "Výchozí pořadí"  # první snímek
    zas = [(0, n - 1)]  # zásobník úseků
    while zas:  # dokud zbývají úseky
        lo, hi = zas.pop()  # vezmeme úsek
        if lo > hi:  # prázdný úsek
            continue  # přeskočit
        if lo == hi:  # jeden prvek
            hot.add(lo)  # je na svém místě
            yield list(a), (lo,), set(hot), f"Úsek s jedním prvkem ({a[lo]}) je hotový"  # snímek
            continue  # další úsek
        pivot = a[(lo + hi) // 2]  # pivot uprostřed
        yield list(a), ((lo + hi) // 2,), set(hot), f"Úsek {lo}–{hi}: pivot = {pivot}"  # snímek: pivot
        lt, i, gt = lo, lo, hi  # tři ukazatele
        while i <= gt:  # dělení úseku
            x = a[i]  # právě zkoumaný prvek
            if x < pivot:  # menší
                a[lt], a[i] = a[i], a[lt]  # doleva
                akt, popis = (lt, i), f"{x} < pivot, jde doleva"  # aktivní prvky a text
                lt += 1;
                i += 1  # posun ukazatelů
            elif x > pivot:  # větší
                a[i], a[gt] = a[gt], a[i]  # doprava
                akt, popis = (i, gt), f"{x} > pivot, jde doprava"  # aktivní prvky a text
                gt -= 1  # zmenšíme pravou hranici
            else:  # rovný
                akt, popis = (i,), f"{x} = pivot, zůstává uprostřed"  # aktivní prvek a text
                i += 1  # posun
            yield list(a), akt, set(hot), popis  # snímek jednoho kroku
        hot.update(range(lt, gt + 1))  # hodnoty rovné pivotu jsou hotové
        yield list(a), tuple(range(lt, gt + 1)), set(hot), f"Hodnoty rovné pivotu {pivot} jsou na místě"
        zas += [(lo, lt - 1), (gt + 1, hi)]  # přidáme levou a pravou část
    yield list(a), (), set(range(n)), "Hotovo"  # závěrečný snímek


def insertion_sort(data):  # Insertion sort = řazení vkládáním
    # PRINCIP: pole má vlevo seřazenou část a vpravo neseřazenou. Zpočátku je seřazený jen první prvek.
    # Vždy vezmeme první prvek neseřazené části (klíč) a "zasuneme" ho do seřazené části na správné místo,
    # tak jak si v ruce seřazujete karty: větší karty posunete doprava a klíč vložíte do vzniklé mezery.
    a = list(data)  # kopie, aby se vstup nezměnil
    for i in range(1, len(a)):  # a[:i] je seřazené, a[i] je prvek, který teď vložíme
        klic = a[i]  # prvek, který si "vezmeme do ruky"
        j = i - 1  # začínáme porovnávat s jeho levým sousedem
        while j >= 0 and a[j] > klic:  # dokud je vlevo větší prvek (ostré >, proto stabilní)
            a[j + 1] = a[j]  # větší prvek posuneme o místo doprava (tím vznikne mezera)
            j -= 1  # jdeme porovnat další prvek vlevo
        a[j + 1] = klic  # klíč vložíme do mezery: vlevo jsou menší nebo rovné, vpravo větší
    return a  # vrátíme seřazené pole


def insertion_kroky(data):  # krokový Insertion sort
    # V animaci se klíč posouvá doleva postupnými výměnami se sousedem (vizuálně je to totéž
    # jako posouvání větších prvků doprava, jen je lépe vidět, kudy klíč putuje).
    a = list(data);
    n = len(a)  # kopie pole a jeho délka
    yield list(a), (), set(), "Výchozí pořadí"  # první snímek
    for i in range(1, n):  # postupně vkládáme prvky z pozic 1..n-1
        klic, j = a[i], i  # klíč a jeho aktuální pozice
        yield list(a), (i,), set(range(i)), (  # snímek: vybraný klíč, zelená = seřazená část vlevo
            f"Vkládám prvek {klic} z pozice {i} do seřazené části (pozice 0–{i - 1})")  # text kroku
        while j > 0 and a[j - 1] > a[j]:  # vlevo je větší prvek -> klíč patří víc doleva
            sused = a[j - 1]  # levý soused, kterého klíč přeskočí
            a[j - 1], a[j] = a[j], a[j - 1]  # klíč se posune o jedno místo doleva
            j -= 1  # klíč je nyní o pozici níž
            yield list(a), (j, j + 1), set(range(i + 1)), f"{klic} < {sused}: posouvám {klic} doleva"  # snímek
        if j == i:  # klíč se vůbec nepohnul
            popis = f"{klic} ≥ levý soused, zůstává na místě"  # text kroku
        else:  # klíč našel nové místo
            popis = f"{klic} našel své místo v seřazené části: pozice {j}"  # text kroku
        yield list(a), (j,), set(range(i + 1)), popis  # snímek: seřazená část je teď o prvek delší
    yield list(a), (), set(range(n)), "Hotovo"  # závěrečný snímek


def _presun_dolu(a, i, n):  # pomocná funkce haldy: "propadnutí" prvku dolů
    # Halda je binární strom uložený v poli: potomci prvku na pozici i jsou na pozicích 2i+1 a 2i+2.
    # V maximové haldě je každý rodič větší nebo roven svým potomkům (největší prvek je tedy na pozici 0).
    # Funkce opraví haldu o n prvcích, pokud je porušená jen v prvku i: prvek posouvá dolů, dokud
    # nebude větší než oba potomci (nebo nedojde do listu).
    while True:  # opakujeme, dokud má prvek smysl posouvat
        l, r, nej = 2 * i + 1, 2 * i + 2, i  # levý potomek, pravý potomek, zatím největší = rodič
        if l < n and a[l] > a[nej]:  # levý potomek existuje a je větší než dosud největší?
            nej = l  # největší je levý potomek
        if r < n and a[r] > a[nej]:  # pravý potomek existuje a je větší než dosud největší?
            nej = r  # největší je pravý potomek
        if nej == i:  # rodič je největší -> halda je v pořádku
            return  # hotovo
        a[i], a[nej] = a[nej], a[i]  # jinak prohodíme rodiče s větším potomkem
        i = nej  # a pokračujeme o patro níž, kde mohla vzniknout chyba


def heap_sort(data):  # Heap sort = řazení haldou
    # PRINCIP: 1) z pole vytvoříme maximovou haldu -> největší prvek je na pozici 0.
    # 2) Opakovaně: největší prvek (vrchol) prohodíme s posledním prvkem haldy. Ten největší je tím na
    #    konečném místě (vzadu), halda se o prvek zmenší a nový vrchol "propadne" dolů, aby halda zase platila.
    #    Po n-1 opakováních je pole seřazené vzestupně.
    a = list(data)  # kopie pole
    n = len(a)  # počet prvků
    for i in range(n // 2 - 1, -1, -1):  # fáze 1: stavba haldy, listy (druhá půlka pole) už jsou haldy
        _presun_dolu(a, i, n)  # opravíme podstrom s kořenem i (od posledního rodiče k vrcholu)
    for konec in range(n - 1, 0, -1):  # fáze 2: halda se zmenšuje, konec = poslední pozice haldy
        a[0], a[konec] = a[konec], a[0]  # největší prvek jde na konec (konečná pozice)
        _presun_dolu(a, 0, konec)  # nový vrchol propadne dolů; halda má teď jen konec prvků
    return a  # vrátíme seřazené pole (výměny na dálku -> nestabilní)


def _presun_dolu_kroky(a, i, n, hot):  # krokový "propad" prvku v haldě
    while True:  # stejná logika jako _presun_dolu, ale s yield
        l, r, nej = 2 * i + 1, 2 * i + 2, i  # potomci a zatím největší
        if l < n and a[l] > a[nej]:  # porovnání s levým potomkem
            nej = l  # nový největší
        if r < n and a[r] > a[nej]:  # porovnání s pravým potomkem
            nej = r  # nový největší
        akt = tuple(x for x in (i, l, r) if x < n)  # aktivní: rodič a jeho existující potomci
        if l >= n:  # prvek nemá žádné potomky (je list)
            yield list(a), akt, set(hot), f"Pozice {i} ({a[i]}) nemá potomky, zůstává"  # snímek
            return  # konec propadu
        if nej == i:  # rodič je největší
            yield list(a), akt, set(hot), f"Rodič {a[i]} (pozice {i}) je větší než potomci, halda platí"  # snímek
            return  # konec propadu
        popis = (f"Rodič {a[i]} (pozice {i}) je menší než potomek {a[nej]} (pozice {nej}) "  # text kroku
                 f"→ prohazuji je")  # dokončení textu
        a[i], a[nej] = a[nej], a[i]  # výměna rodiče s větším potomkem
        yield list(a), akt, set(hot), popis  # snímek po výměně
        i = nej  # pokračujeme v nižším patře


def heap_kroky(data):  # krokový Heap sort
    a = list(data);
    n = len(a);
    hot = set()  # kopie, délka, hotové indexy
    yield list(a), (), set(), "Výchozí pořadí"  # první snímek
    if n < 2:  # prázdné pole nebo jeden prvek je už seřazený (a[0] by u prázdného pole neexistovalo)
        yield list(a), (), set(range(n)), "Hotovo"  # rovnou závěrečný snímek
        return  # konec generátoru
    yield list(a), (), set(), ("Fáze 1: stavím maximovou haldu (rodič ≥ potomci). "  # vysvětlení fáze 1
                               "Potomci pozice i jsou 2i+1 a 2i+2.")  # dokončení textu
    for i in range(n // 2 - 1, -1, -1):  # od posledního rodiče k vrcholu
        yield from _presun_dolu_kroky(a, i, n, hot)  # opravíme podstrom
    yield list(a), (0,), set(), f"Halda je hotová: největší prvek {a[0]} je na vrcholu (pozice 0)"  # konec fáze 1
    for konec in range(n - 1, 0, -1):  # fáze 2: halda se zmenšuje
        a[0], a[konec] = a[konec], a[0]  # největší prvek na konec haldy
        hot.add(konec)  # tato pozice je konečná
        yield list(a), (0, konec), set(hot), (  # snímek výměny
            f"Fáze 2: největší prvek {a[konec]} z vrcholu jde na pozici {konec} (hotovo)")  # text kroku
        yield from _presun_dolu_kroky(a, 0, konec, hot)  # nový vrchol propadne v zmenšené haldě
    yield list(a), (), set(range(n)), "Hotovo"  # závěrečný snímek


# název: (funkce, krokový generátor, složitost a stabilita, princip pro animaci)
ALG = {  # slovník všech algoritmů
    "Bubble sort": (bubble_sort, bubble_kroky, "O(n²), stabilní",  # funkce, kroky, vlastnosti
                    "Porovnává sousední prvky a vymění je, pokud jsou ve špatném pořadí. Po každém průchodu je největší "
                    "zbývající hodnota na konci. Průchody se opakují, dokud už není potřeba žádná výměna."),
    "Selection sort": (selection_sort, selection_kroky, "O(n²), nestabilní",
                       "V neseřazené části najde nejmenší prvek a prohodí ho s jejím prvním prvkem. "
                       "Seřazená část vlevo tak vždy povyroste o jeden prvek."),
    "Merge sort": (merge_sort, merge_kroky, "O(n log n), stabilní",
                   "Pole opakovaně půlí, až zůstanou úseky o jednom prvku. Potom vždy dvě seřazené poloviny slije: "
                   "porovná jejich první prvky a menší zapíše do výsledku."),
    "Quick sort": (quick_sort, quick_kroky, "průměr O(n log n), až O(n²), nestabilní",
                   "Vybere pivot a pole rozdělí na menší, rovné a větší prvky. Prvky rovné pivotu jsou hotové. "
                   "Stejně pak řadí levou a pravou část."),
    "Insertion sort": (insertion_sort, insertion_kroky, "O(n²), stabilní",
                       "Pole má vlevo seřazenou část (zelená). Další prvek z neseřazené části se vloží na správné místo "
                       "v seřazené části: větší prvky se posunou doprava a vkládaný prvek jde do vzniklé mezery."),
    "Heap sort": (heap_sort, heap_kroky, "O(n log n), nestabilní",
                  "Pole chápe jako binární strom (potomci pozice i jsou 2i+1 a 2i+2) a vytvoří z něj maximovou haldu: "
                  "rodič je vždy větší než potomci. Největší prvek z vrcholu pak opakovaně prohodí s koncem haldy "
                  "(tam je hotový) a nový vrchol nechá propadnout dolů."),
}


# ===================== DATA =====================
def temer_serazene(r, n):  # téměř seřazená data
    a = sorted(r.randint(1, 100000) for _ in range(n))  # nejdřív seřazená čísla
    for _ in range(max(1, n // 20)):  # cca 5 % náhodných výměn
        i, j = r.randrange(n), r.randrange(n)  # dvě náhodné pozice
        a[i], a[j] = a[j], a[i]  # prohodíme je
    return a  # vrátíme pole


ROZ = {  # typy rozložení dat
    "Náhodně": lambda r, n: [r.randint(1, 100000) for _ in range(n)],  # rovnoměrně náhodná čísla
    "Normální": lambda r, n: [min(100000, max(1, round(r.gauss(50000, 15000)))) for _ in range(n)],  # zvonovité
    "Téměř seřazené": temer_serazene,  # skoro seřazené
    "Opačně seřazené": lambda r, n: sorted((r.randint(1, 100000) for _ in range(n)), reverse=True),  # sestupně
    "Mnoho duplicit": lambda r, n: [r.randint(1, 10) for _ in range(n)],  # jen čísla 1–10
}


def cisla(text):  # převod textu na čísla
    """Text -> čísla; oddělovače: mezera, nový řádek, středník, čárka."""
    vysl = []  # seznam čísel
    for t in re.split(r"[\s;,]+", text.strip()):  # rozdělíme podle oddělovačů
        if t:  # přeskočíme prázdné části
            try:  # pokus o převod
                v = float(t)  # text -> číslo
            except ValueError:  # nejde převést
                raise ValueError(f"„{t}“ není číslo") from None  # srozumitelná chyba
            if not math.isfinite(v):  # odmítneme nan a inf
                raise ValueError(f"„{t}“ není číslo")  # chyba
            vysl.append(int(v) if v.is_integer() else v)  # celé číslo ukládáme jako int
    return vysl  # vrátíme čísla


# ===================== GUI =====================
BG, TL, POLE, FG = "#2b2b2b", "#4a4a4a", "#1c1c1c", "#e6e6e6"  # pozadí, tlačítka, pole, text
ORA, MOD, ZEL = "#ff9f1c", "#5aa9ff", "#34c759"  # oranžová, modrá, zelená
SIRKA = 34  # šířka jednoho sloupce v grafu


def styl(root):  # nastavení tmavého vzhledu
    s = ttk.Style(root)  # objekt stylů
    s.theme_use("clam")  # motiv, který jde dobře přebarvit
    root.configure(bg=BG)  # tmavé pozadí okna
    root.option_add("*TCombobox*Listbox.background", POLE)  # tmavý rozbalovací seznam
    root.option_add("*TCombobox*Listbox.foreground", FG)  # světlý text v seznamu
    s.configure(".", background=BG, foreground=FG, fieldbackground=POLE, bordercolor="#555",  # základ
                lightcolor=TL, darkcolor=TL, troughcolor=POLE, insertcolor=FG, arrowcolor=FG)  # všech prvků
    s.configure("TButton", background=TL, padding=(10, 3))  # vzhled tlačítek
    s.map("TButton", background=[("active", "#5a5a5a"), ("disabled", "#333")],  # hover a neaktivní stav
          foreground=[("disabled", "#777")])  # šedý text u neaktivního tlačítka
    s.map("TCheckbutton",  # OPRAVA: zaškrtávátka při najetí myší
          background=[("active", BG)],  # pozadí zůstane tmavé (dřív bílé)
          foreground=[("active", FG)],  # text zůstane světlý, je vidět
          indicatorcolor=[("selected", "#3b82f6"), ("!selected", POLE)])  # modrý čtvereček když je zaškrtnuto
    s.map("TCombobox", fieldbackground=[("readonly", POLE)])  # tmavé rozbalovací pole
    s.configure("Treeview", background=POLE, fieldbackground=POLE, rowheight=22)  # tabulka
    s.configure("Treeview.Heading", background="#3a3a3a", relief="flat")  # hlavička tabulky
    s.configure("TNotebook.Tab", background=BG, padding=(12, 4))  # záložky
    s.map("TNotebook.Tab", background=[("selected", TL)])  # vybraná záložka je světlejší


class Animace(tk.Toplevel):  # okno s animací řazení
    def __init__(self, rodic, nazev, data):  # vytvoření okna
        super().__init__(rodic)  # okno patří hlavnímu oknu
        self.title(f"Animace • {nazev}")  # titulek okna
        self.configure(bg=BG)  # tmavé pozadí
        self.geometry("820x540")  # velikost okna
        self.kroky = list(ALG[nazev][1](data))  # všechny kroky spočítáme předem
        self.i, self.job = 0, None  # číslo kroku a časovač
        self.rych = tk.DoubleVar(value=5)  # rychlost (kroků za sekundu)
        ttk.Label(self, text=nazev, font=("TkDefaultFont", 20, "bold")).pack(anchor="w", padx=12, pady=(10, 0))  # název
        ttk.Label(self, text=ALG[nazev][3], wraplength=780, justify="left").pack(anchor="w", padx=12, pady=4)  # princip
        ttk.Label(self, text="Oranžová: aktivní prvky  •  Modrá: ostatní prvky  •  Zelená: hotovo").pack(anchor="w",
                                                                                                         padx=12)  # legenda
        ram = ttk.Frame(self);
        ram.pack(fill="both", expand=True, padx=12, pady=8)  # rámeček pro graf
        sb = ttk.Scrollbar(ram, orient="horizontal");
        sb.pack(side="bottom", fill="x")  # vodorovný posuvník
        self.pl = tk.Canvas(ram, bg="#131c2e", highlightthickness=0, xscrollcommand=sb.set)  # plátno grafu
        self.pl.pack(fill="both", expand=True)  # plátno vyplní rámeček
        sb.config(command=self.pl.xview)  # posuvník ovládá plátno
        self.pl.bind("<Configure>", lambda e: self.kresli())  # při změně velikosti překreslit
        r = ttk.Frame(self);
        r.pack(fill="x", padx=12)  # řádek s tlačítky
        self.b = ttk.Button(r, text="Přehrát", command=self.prehraj);
        self.b.pack(side="left")  # Přehrát/Pauza
        ttk.Button(r, text="Jeden krok", command=self.dalsi).pack(side="left", padx=6)  # další krok
        ttk.Button(r, text="Od začátku", command=self.zacatek).pack(side="left")  # reset
        ttk.Label(r, text="Rychlost:").pack(side="left", padx=(16, 6))  # popisek posuvníku
        self.lr = ttk.Label(r, text="5 kroků / s", width=12)  # zobrazená rychlost
        ttk.Scale(r, from_=1, to=200, variable=self.rych, length=220,  # posuvník rychlosti
                  command=lambda v: self.lr.config(text=f"{float(v):.0f} kroků / s")).pack(
            side="left")  # aktualizace textu
        self.lr.pack(side="left", padx=6)  # umístění textu rychlosti
        ttk.Button(r, text="Zavřít", command=self.zavri).pack(side="right")  # zavření okna
        self.popis = ttk.Label(self, wraplength=780, justify="left");
        self.popis.pack(anchor="w", padx=12, pady=8)  # popis kroku
        self.protocol("WM_DELETE_WINDOW", self.zavri)  # křížek okna také zastaví časovač

    def kresli(self):  # vykreslení aktuálního kroku
        pole, akt, hot, popis = self.kroky[self.i]  # data aktuálního snímku
        self.popis.config(text=f"Krok {self.i} z {len(self.kroky) - 1} • {popis}")  # text kroku
        c = self.pl  # zkratka na plátno
        c.delete("all")  # smažeme starý obrázek
        h, n = max(c.winfo_height(), 150), len(pole)  # výška plátna a počet sloupců
        lo, hi = min(pole), max(pole)  # nejmenší a největší hodnota
        rozsah = (hi - lo) or 1  # rozsah (nulou nedělíme)
        c.config(scrollregion=(0, 0, n * SIRKA, h))  # oblast, kterou lze posouvat
        for k, v in enumerate(pole):  # nakreslíme každý sloupec
            x = k * SIRKA  # vodorovná pozice sloupce
            vyska = 6 + (v - lo) / rozsah * (h - 70)  # výška sloupce ~ hodnota
            barva = ORA if k in akt else ZEL if k in hot else MOD  # oranžová / zelená / modrá
            c.create_rectangle(x + 3, h - 40 - vyska, x + SIRKA - 3, h - 40, fill=barva, outline="")  # sloupec
            c.create_text(x + SIRKA / 2, h - 28, text=f"{v:g}", fill=FG, font=("TkDefaultFont", 8))  # hodnota
            c.create_text(x + SIRKA / 2, h - 12, text=str(k), fill="#8a94a6", font=("TkDefaultFont", 8))  # pozice
        if akt:  # je nějaký aktivní prvek?
            c.xview_moveto(max(0, (akt[0] * SIRKA - c.winfo_width() / 2) / (n * SIRKA)))  # graf ho následuje

    def prehraj(self):  # tlačítko Přehrát / Pauza
        if self.job:  # už se přehrává?
            return self.pauza()  # pak pozastavit
        if self.i >= len(self.kroky) - 1:  # jsme na konci?
            self.i = 0  # začneme znovu
        self.b.config(text="Pauza")  # tlačítko změní text
        self.tik()  # spustíme přehrávání

    def tik(self):  # jeden tik animace
        if self.i < len(self.kroky) - 1:  # zbývají kroky?
            self.i += 1  # posun na další krok
            self.kresli()  # překreslení
            self.job = self.after(int(1000 / self.rych.get()), self.tik)  # naplánujeme další tik
        else:  # konec animace
            self.pauza()  # zastavit

    def pauza(self):  # zastavení přehrávání
        if self.job:  # běží časovač?
            self.after_cancel(self.job)  # zrušíme ho
        self.job = None  # už nic neběží
        self.b.config(text="Přehrát")  # tlačítko zpět na Přehrát

    def dalsi(self):  # tlačítko Jeden krok
        self.pauza()  # nejdřív zastavit přehrávání
        self.i = min(self.i + 1, len(self.kroky) - 1)  # o krok dál, ne za konec
        self.kresli()  # překreslit

    def zacatek(self):  # tlačítko Od začátku
        self.pauza()  # zastavit přehrávání
        self.i = 0  # zpět na první krok
        self.kresli()  # překreslit

    def zavri(self):  # zavření okna animace
        self.pauza()  # zrušit časovač
        self.destroy()  # zavřít okno


class App(tk.Tk):  # hlavní okno aplikace
    def __init__(self):  # sestavení okna
        super().__init__()  # inicializace Tk
        self.title("Třídící aplikace")  # titulek okna
        self.geometry("820x760")  # velikost okna
        styl(self)  # tmavý vzhled
        self.data, self.vysl = [], []  # data k řazení a výsledky měření
        self.pocet, self.seed = tk.StringVar(value="1000"), tk.StringVar(value="42")  # počet a seed
        self.roz, self.opak = tk.StringVar(value="Náhodně"), tk.StringVar(value="3")  # rozložení a opakování
        self.vyber = {n: tk.BooleanVar(value=True) for n in ALG}  # zaškrtnuté algoritmy
        ttk.Label(self, text="Třídící aplikace", font=("TkDefaultFont", 20, "bold")).pack(anchor="w", padx=12,
                                                                                          pady=(10, 0))  # nadpis
        ttk.Label(self, text="Stejná data. Šest algoritmů. Porovnání skutečné doby třídění.").pack(anchor="w",
                                                                                                    padx=12)  # podnadpis

        f1 = ttk.LabelFrame(self, text=" 1  Připravte data ", padding=8)  # sekce 1
        f1.pack(fill="x", padx=12, pady=8)  # umístění sekce
        r = ttk.Frame(f1);
        r.pack(fill="x")  # první řádek sekce
        ttk.Label(r, text="Počet").pack(side="left")  # popisek počtu
        ttk.Entry(r, textvariable=self.pocet, width=8).pack(side="left", padx=(6, 14))  # pole počtu
        ttk.Label(r, text="Seed").pack(side="left")  # popisek seedu
        ttk.Entry(r, textvariable=self.seed, width=8).pack(side="left", padx=(6, 14))  # pole seedu
        ttk.Combobox(r, textvariable=self.roz, values=list(ROZ), state="readonly", width=16).pack(
            side="left")  # typ rozložení
        ttk.Button(r, text="Generovat data", command=self.generuj).pack(side="left", padx=8)  # generování
        ttk.Button(r, text="Načíst TXT…", command=self.soubor).pack(side="right")  # načtení souboru
        ttk.Label(f1, text="Ruční vstup: mezery, nové řádky nebo středníky.").pack(anchor="w", pady=(8, 2))  # nápověda
        r = ttk.Frame(f1);
        r.pack(fill="x")  # řádek s ručním vstupem
        self.rucne = ttk.Entry(r)  # pole pro ruční zadání
        self.rucne.insert(0, "12 -5 8 0 12 3")  # ukázková hodnota
        self.rucne.pack(side="left", fill="x", expand=True)  # pole se roztáhne
        ttk.Button(r, text="Použít ruční vstup", command=self.rucni).pack(side="right", padx=(8, 0))  # potvrzení
        self.info = ttk.Label(f1);
        self.info.pack(anchor="w", pady=(6, 0))  # info o aktuálních datech

        f2 = ttk.LabelFrame(self, text=" 2  Vyberte algoritmy ", padding=8)  # sekce 2
        f2.pack(fill="x", padx=12)  # umístění sekce
        for k, (n, a) in enumerate(ALG.items()):  # zaškrtávátko pro každý algoritmus
            ttk.Checkbutton(f2, text=f"{n}  •  {a[2]}", variable=self.vyber[n], command=self.tlacitka).grid(
                # název + vlastnosti
                row=k // 2, column=k % 2, sticky="w", padx=(0, 40), pady=1)  # mřížka 2 sloupce
        r = ttk.Frame(f2);
        r.grid(row=(len(ALG) + 1) // 2, column=0, columnspan=2, sticky="w", pady=(8, 0))  # řádek s tlačítky
        ttk.Button(r, text="Vše", command=lambda: self.nastav(True)).pack(side="left")  # zaškrtnout vše
        ttk.Button(r, text="Nic", command=lambda: self.nastav(False)).pack(side="left", padx=6)  # odškrtnout vše
        ttk.Label(r, text="Opakování (1–10):").pack(side="left", padx=(8, 4))  # popisek opakování
        ttk.Spinbox(r, from_=1, to=10, textvariable=self.opak, width=3).pack(side="left")  # počet opakování
        self.b_por = ttk.Button(r, text="Porovnat algoritmy", command=self.porovnej);
        self.b_por.pack(side="left", padx=8)  # porovnání
        self.b_anim = ttk.Button(r, text="Animovat", command=self.animuj);
        self.b_anim.pack(side="left")  # animace

        nb = ttk.Notebook(self)  # záložky
        nb.pack(fill="both", expand=True, padx=12, pady=8)  # umístění záložek
        t3 = ttk.Frame(nb, padding=8);
        nb.add(t3, text="3  Porovnání časů")  # záložka s tabulkou
        sl = ("a", "med", "min", "max", "s")  # sloupce tabulky
        self.tab = ttk.Treeview(t3, columns=sl, show="headings", height=len(ALG))  # tabulka výsledků (řádek pro každý algoritmus)
        for c, t in zip(sl, ("Algoritmus", "Medián (ms)", "Minimum (ms)", "Maximum (ms)", "Stav")):  # nadpisy sloupců
            self.tab.heading(c, text=t)  # nastavení nadpisu
            self.tab.column(c, anchor="w" if c == "a" else "center", width=150 if c == "a" else 130 if c != "s" else 95)  # zarovnání a šířka (součet se vejde do okna)
        self.tab.pack(fill="both", expand=True)  # umístění tabulky
        self.nej = ttk.Label(t3, text="Nejrychlejší algoritmus: –");
        self.nej.pack(anchor="w", pady=4)  # nejrychlejší
        ttk.Button(t3, text="Export porovnání do CSV…", command=self.export).pack(anchor="w")  # export
        t4 = ttk.Frame(nb, padding=8);
        nb.add(t4, text="Náhled dat")  # záložka s náhledem dat
        self.nahled = tk.Text(t4, height=6, bg=POLE, fg=FG, relief="flat", wrap="word")  # textové pole náhledu
        self.nahled.pack(fill="both", expand=True)  # umístění náhledu
        ttk.Label(self, text=f"Pomalé metody (Bubble, Selection, Insertion): max. {MAX_POMALE} prvků. "  # upozornění
                             f"Animace: jeden algoritmus a max. {MAX_ANIM} hodnot.").pack(anchor="w",
                                                                                          padx=12)  # na limity
        self.stav = ttk.Label(self, text="Připraveno.");
        self.stav.pack(anchor="w", padx=12, pady=(0, 8))  # stavový řádek
        self.generuj()  # na začátku vygenerujeme data

    def chyba(self, text):  # zobrazení chybové hlášky
        messagebox.showerror("Chyba", text)  # okno s chybou

    def nastav_data(self, d, zdroj):  # uloží nová data
        if not 1 <= len(d) <= MAX_N:  # kontrola počtu
            return self.chyba(f"Zadej 1 až {MAX_N} čísel.")  # chyba při špatném počtu
        self.data = d  # uložíme data
        self.info.config(text=f"{len(d)} hodnot • {zdroj}")  # info pod ručním vstupem
        self.nahled.delete("1.0", "end")  # smažeme starý náhled
        self.nahled.insert("1.0", " ".join(map(str, d[:2000])) + (" …" if len(d) > 2000 else ""))  # nový náhled
        self.tlacitka()  # aktualizace tlačítek

    def generuj(self):  # generování náhodných dat
        try:  # ošetříme špatný vstup
            n = int(self.pocet.get())  # počet prvků
        except ValueError:  # není to celé číslo
            n = 0  # vyvolá chybu níže
        if not 1 <= n <= MAX_N:  # kontrola rozsahu
            return self.chyba(f"Počet musí být celé číslo 1 až {MAX_N}.")  # chyba
        r = random.Random(self.seed.get() or None)  # stejný seed = stejná data
        self.nastav_data(ROZ[self.roz.get()](r, n), f"Generátor, seed {self.seed.get()}, {self.roz.get()}")  # uložení

    def soubor(self):  # načtení celých čísel ze souboru TXT
        cesta = filedialog.askopenfilename(
            title="Vyberte TXT soubor s čísly",
            filetypes=[("Textové soubory", "*.txt")]
        )
        if not cesta:  # uživatel výběr zrušil
            return
        try:
            with open(cesta, "r", encoding="utf-8-sig") as f:
                obsah = f.read()
            hodnoty = obsah.replace(",", " ").replace(";", " ").split()
            if not hodnoty:
                raise ValueError("Soubor neobsahuje žádná čísla.")
            data = []
            for hodnota in hodnoty:
                try:
                    data.append(int(hodnota))  # zatím přijímáme pouze celá čísla
                except ValueError:
                    raise ValueError(f"Neplatné celé číslo: {hodnota}") from None
            self.nastav_data(data, f"TXT soubor: {cesta.rsplit('/', 1)[-1].rsplit(chr(92), 1)[-1]}")
        except (OSError, UnicodeError, ValueError) as e:
            self.chyba(f"Soubor nelze načíst: {e}")

    def rucni(self):  # použití ručního vstupu
        try:  # převod může selhat
            self.nastav_data(cisla(self.rucne.get()), "ruční vstup")  # text -> čísla -> data
        except ValueError as e:  # špatný vstup
            self.chyba(str(e))  # zobrazíme chybu

    def nastav(self, hodnota):  # tlačítka Vše / Nic
        for v in self.vyber.values():  # projdeme všechna zaškrtávátka
            v.set(hodnota)  # zaškrtneme / odškrtneme
        self.tlacitka()  # aktualizace tlačítek

    def tlacitka(self):  # povolí / zakáže tlačítka
        pocet = sum(v.get() for v in self.vyber.values())  # kolik algoritmů je vybráno
        self.b_por.state(["!disabled" if self.data and pocet else "disabled"])  # porovnat: aspoň 1 algoritmus
        self.b_anim.state(["!disabled" if self.data and pocet == 1 else "disabled"])  # animovat: právě 1

    def porovnej(self):  # změření časů algoritmů
        try:  # ošetříme špatné opakování
            opak = int(self.opak.get())  # počet opakování
        except ValueError:  # není to číslo
            opak = 0  # vyvolá chybu níže
        if not 1 <= opak <= 10:  # kontrola rozsahu
            return self.chyba("Počet opakování musí být 1 až 10.")  # chyba
        self.vysl = []  # vymažeme staré výsledky
        self.tab.delete(*self.tab.get_children())  # vyprázdníme tabulku
        for n, a in ALG.items():  # projdeme algoritmy
            if not self.vyber[n].get():  # není vybraný?
                continue  # přeskočit
            d = self.data[:MAX_POMALE] if n in POMALE else self.data  # pomalé algoritmy omezíme
            self.stav.config(text=f"Měřím {n}…")  # zpráva o průběhu
            self.update()  # překreslení okna
            casy = []  # naměřené časy
            for _ in range(opak):  # opakované měření
                t0 = time.perf_counter()  # start stopek
                vysledek = a[0](d)  # spuštění řazení
                casy.append((time.perf_counter() - t0) * 1000)  # čas v milisekundách
            stav = "Ověřeno" if vysledek == sorted(d) else "CHYBA"  # kontrola proti sorted()
            self.vysl.append((n, statistics.median(casy), min(casy), max(casy), stav))  # medián, min, max
            self.tab.insert("", "end", values=(n, *(f"{x:.4f}" for x in self.vysl[-1][1:4]), stav))  # řádek tabulky
        dobre = [v for v in self.vysl if v[4] == "Ověřeno"]  # správně seřazené
        if dobre:  # máme aspoň jeden správný
            nej = min(dobre, key=lambda v: v[1])  # nejmenší medián
            self.nej.config(text=f"Nejrychlejší algoritmus: {nej[0]} — {nej[1]:.4f} ms (medián)."  # text
                                 + (f" Pomalé metody měřeny jen na {MAX_POMALE} prvcích." if len(
                self.data) > MAX_POMALE else ""))  # upozornění
        self.stav.config(text="Hotovo. Všechny výsledky odpovídají sorted()." if len(dobre) == len(self.vysl)  # vše OK
        else "Pozor: některý výsledek neodpovídá sorted()!")  # něco je špatně

    def export(self):  # export výsledků do CSV
        if not self.vysl:  # nic neměřeno
            return self.chyba("Nejdřív porovnej algoritmy.")  # chyba
        cesta = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")])  # kam uložit
        if cesta:  # uživatel vybral soubor
            with open(cesta, "w", newline="", encoding="utf-8-sig") as f:  # BOM kvůli českému Excelu
                w = csv.writer(f, delimiter=";")  # středník jako oddělovač
                w.writerow(["Algoritmus", "Medián (ms)", "Minimum (ms)", "Maximum (ms)", "Stav"])  # hlavička
                for n, med, mn, mx, s in self.vysl:  # řádky s výsledky
                    w.writerow([n, *(f"{x:.4f}".replace(".", ",") for x in (med, mn, mx)), s])  # desetinná čárka

    def animuj(self):  # otevře okno animace
        nazev = next(n for n, v in self.vyber.items() if v.get())  # jediný vybraný algoritmus
        if len(self.data) > MAX_ANIM:  # dat je moc
            messagebox.showinfo("Animace", f"Animace použije jen prvních {MAX_ANIM} hodnot.")  # upozornění
        Animace(self, nazev, self.data[:MAX_ANIM])  # okno animace s prvními 100 hodnotami


if __name__ == "__main__":  # spustí se jen přímým během souboru
    App().mainloop()  # vytvoření okna a hlavní smyčka
