<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente, it.unisa.uniclass.utenti.model.Tipo" %>

<%
    /* Sessione HTTP */
    HttpSession sessione = request.getSession(true);
    Utente user = (Utente) sessione.getAttribute("currentSessionUser");

    if (user != null) {
        sessione.setAttribute("utenteEmail", user.getEmail());
    }

    Tipo tipoUtente = (user != null) ? (Tipo) user.getTipo() : null;
%>

<!DOCTYPE html>
<html lang="it">
<head>
    <title>Mappa UniSA - Eco-Friendly Version</title>
    <meta name="viewport" content="width=device-width, initial-scale=1">

    <script src="scripts/sidebar.js" defer></script>
    <link rel="stylesheet" href="styles/headerStyle.css">
    <link rel="stylesheet" href="styles/barraNavigazioneStyle.css">
    <link rel="stylesheet" href="styles/mappa.css">
    <link rel="stylesheet" href="styles/footerstyle.css">

    <link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css"
          integrity="sha256-p4NxAoJBhIIN+hmNHrzRCf9tD/miZyoHS5obTRR9BMY=" crossorigin=""/>

    <link rel="icon" href="images/logois.webp" type="image/webp">
</head>

<body>

<div class="barraNavigazione" id="barraNavigazione">
    <a href="javascript:void(0)" class="closebtn" onclick="closeNav()">
        <img src="images/icons/menuOpenIcon.webp" alt="Chiudi menu">
    </a>
    <p>Menu</p>
    <ul id="menu">
        <li><a href="aula.jsp">Aule</a></li>
        <% if (tipoUtente != null && !tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li><a href="Conversazioni">Conversazioni</a></li>
        <% } else if (tipoUtente != null && tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
        <% } %>
        <li><a href="mappa.jsp">Mappa</a></li>
        <li><a href="ChatBot.jsp">ChatBot</a></li>
        <li><a href="infoapp.jsp">Info App</a></li>
        <li><a href="aboutus.jsp">Chi Siamo</a></li>
    </ul>
</div>

<jsp:include page="header.jsp"/>

<main>
    <section class="map-section">
        <h1>Mappa dell'Università degli Studi di Salerno</h1>
        <p style="text-align: center; font-size: 0.9em; color: #666;">Versione ottimizzata per il risparmio energetico</p>

        <div class="map-container" id="mapContainer">
            <img id="staticMap"
                 src="images/unisa-map-static.webp"
                 alt="Mappa statica dell'Università degli Studi di Salerno"
                 class="map"
                 width="1000"
                 height="700"
                 loading="lazy">

            <button id="loadMapBtn" class="load-map-btn" onclick="loadInteractiveMap()">
                Apri mappa interattiva
            </button>

            <noscript>
                <p>JavaScript è disabilitato. <a href="https://www.google.com/maps">Apri su Google Maps</a></p>
            </noscript>
        </div>
    </section>
</main>

<%@ include file="footer.jsp" %>

<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js"
        integrity="sha256-20nQCchB9co0qIjJZRGuk2/Z9VM+kNiyxNV1lvTlZBo=" crossorigin=""></script>

<script>
    let mapInitialized = false;

    function loadInteractiveMap() {
        if (mapInitialized) return;
        mapInitialized = true;

        const container = document.getElementById("mapContainer");
        const btn = document.getElementById("loadMapBtn");
        const img = document.getElementById("staticMap");

        // Rimuoviamo asset statici per fare spazio al div della mappa
        if(btn) btn.remove();
        if(img) img.remove();

        // Creiamo il div per Leaflet
        const mapDiv = document.createElement('div');
        mapDiv.id = 'leafletMap';
        mapDiv.className = 'map'; // Riutilizziamo la classe CSS esistente
        mapDiv.style.height = "700px";
        mapDiv.style.width = "100%";
        container.appendChild(mapDiv);

        // INIZIALIZZAZIONE SOSTENIBILE
        const map = L.map('leafletMap', {
            preferCanvas: true, // RIDUCE NODI DOM (Impatto EcoIndex)
            wheelDebounceTime: 150
        }).setView([40.775, 14.789], 16);

        // Tile Layer leggero (OpenStreetMap)
        L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
            attribution: '&copy; OSM contributors',
            maxZoom: 19
        }).addTo(map);

        // ESEMPIO MARKER SOSTENIBILI (CircleMarkers invece di icone PNG/SVG esterne)
        // Questo elimina le richieste HTTP per aulaLibera.png e aulaOccupata.png
        const aule = [
            { nome: "Aula Magna", coords: [40.7752, 14.7891], stato: "libera" },
            { nome: "Laboratorio F", coords: [40.7745, 14.7885], stato: "occupata" }
        ];

        aule.forEach(aula => {
            L.circleMarker(aula.coords, {
                radius: 10,
                fillColor: aula.stato === "libera" ? "#28a745" : "#dc3545",
                color: "#fff",
                weight: 2,
                fillOpacity: 0.8
            }).addTo(map).bindPopup(`<b>${aula.nome}</b><br>Stato: ${aula.stato}`);
        });
    }

    // LAZY LOADING AVANZATO: Carica la mappa quando l'utente la raggiunge con lo scroll
    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                loadInteractiveMap();
                observer.unobserve(entry.target);
            }
        });
    }, { rootMargin: '100px' });

    observer.observe(document.getElementById('mapContainer'));
</script>

</body>
</html>