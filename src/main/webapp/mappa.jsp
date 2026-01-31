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
	<title>Mappa UniSA - Sostenibile</title>
	<meta name="viewport" content="width=device-width, initial-scale=1">

	<script src="scripts/sidebar.js" defer></script>
	<link rel="stylesheet" href="styles/headerStyle.css">
	<link rel="stylesheet" href="styles/barraNavigazioneStyle.css">
	<link rel="stylesheet" href="styles/mappa.css">
	<link rel="stylesheet" href="styles/footerstyle.css">

	<link rel="stylesheet" href="https://unpkg.com/leaflet@1.9.4/dist/leaflet.css" integrity="sha256-p4NxAoJBhIIN+hmNHrzRCf9tD/miZyoHS5obTRR9BMY=" crossorigin=""/>

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
		<% if (tipoUtente != null && (tipoUtente.equals(Tipo.Studente) || tipoUtente.equals(Tipo.Docente) || tipoUtente.equals(Tipo.Coordinatore))) { %>
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
<br><br>

<main>
	<section class="map-section">
		<h1>Mappa dell'Università degli Studi di Salerno</h1>

		<div class="map-container" id="map-parent">
			<img id="static-map-img"
				 src="images/unisa-map-static.webp"
				 alt="Mappa statica dell'Università degli Studi di Salerno"
				 class="map"
				 width="1000"
				 height="700"
				 loading="lazy">

			<button id="load-map-btn" class="load-map-btn" onclick="loadInteractiveMap()">
				Apri mappa interattiva
			</button>

			<noscript>
				<p>JavaScript è disabilitato. <a href="https://www.openstreetmap.org/#map=16/40.775/14.789">Apri la mappa su OSM</a></p>
			</noscript>
		</div>
	</section>
</main>

<%@ include file="footer.jsp" %>

<script src="https://unpkg.com/leaflet@1.9.4/dist/leaflet.js" integrity="sha256-20nQCchB9co0qIjJZRGuk2/Z9VM+kNiyxNV1lvTlZBo=" crossorigin=""></script>

<script>
	let isMapLoaded = false;

	function loadInteractiveMap() {
		if (isMapLoaded) return;
		isMapLoaded = true;

		const parent = document.getElementById("map-parent");
		const btn = document.getElementById("load-map-btn");
		const img = document.getElementById("static-map-img");

		// Rimuoviamo gli elementi statici per risparmiare memoria
		if (btn) btn.remove();
		if (img) img.remove();

		// Creiamo il div per la mappa Leaflet
		const mapDiv = document.createElement('div');
		mapDiv.id = 'map';
		mapDiv.className = 'map';
		mapDiv.style.height = "700px";
		mapDiv.style.width = "100%";
		parent.appendChild(mapDiv);

		// ABILITAZIONE RENDERING SU CANVAS (Ottimizzazione EcoIndex)
		// Invece di SVG individuali, usa un unico canvas per tutti i marker
		const map = L.map('map', {
			preferCanvas: true
		}).setView([40.775, 14.789], 16);

		// Tile layer leggero da OpenStreetMap
		L.tileLayer('https://{s}.tile.openstreetmap.org/{z}/{x}/{y}.png', {
			attribution: '© OpenStreetMap contributors'
		}).addTo(map);

		// ESEMPIO MARKER SOSTENIBILI (CircleMarker invece di PNG pesanti)
		L.circleMarker([40.775, 14.789], {
			radius: 10,
			fillColor: "#28a745",
			color: "#fff",
			weight: 2,
			fillOpacity: 0.8
		}).addTo(map).bindPopup("<b>Campus di Fisciano</b><br>Università di Salerno.");
	}

	// LAZY LOADING AUTOMATICO (Intersection Observer)
	// Se l'utente scorre fino alla mappa, la carichiamo senza aspettare il click
	const observer = new IntersectionObserver((entries) => {
		entries.forEach(entry => {
			if (entry.isIntersecting) {
				loadInteractiveMap();
				observer.unobserve(entry.target);
			}
		});
	}, { rootMargin: '200px' });

	observer.observe(document.getElementById('map-parent'));
</script>

</body>
</html>