<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.model.Utente, it.unisa.uniclass.utenti.model.Tipo" %>

<%
	/* Sessione HTTP */
	HttpSession sessione = request.getSession(true);
	Utente user = (Utente) sessione.getAttribute("currentSessionUser");
	if(user != null){
		session.setAttribute("utenteEmail", user.getEmail());
	}

	/* Controllo tipo utente */
	Tipo tipoUtente;
	if(user != null)
		tipoUtente = (Tipo) user.getTipo();
	else
		tipoUtente = null;
%>

<!DOCTYPE html>
<html lang="it">
<head>
	<title>UniClass ChatBot</title>
	<script src="scripts/sidebar.js" type="text/javascript"></script>
	<script src="scripts/chatBotJS.js"></script>
	<link type="text/css" rel="stylesheet" href="styles/headerStyle.css"/>
	<link type="text/css" rel="stylesheet" href="styles/barraNavigazioneStyle.css" />
	<link type="text/css" rel="stylesheet" href="styles/chatbot.css"/>
	<link type="text/css" rel="stylesheet" href="styles/footerstyle.css">
	<link rel="icon" href="images/logois.png" sizes="32x32" type="image/png">
</head>
<body>

<%-- ===== BARRA NAVIGAZIONE ===== --%>

<div class="barraNavigazione" id="barraNavigazione">

	<button type="button" class="closebtn" onclick="closeNav()" aria-label="Chiudi menu">
		<img src="images/icons/menuOpenIcon.png" alt="Chiudi menu">
	</button>

	<p>Menu</p>
	<ul id="menu">
		<% if(tipoUtente == null) { %>
		<li><a href="aula.jsp">Aule</a></li>
		<li><a href="mappa.jsp">Mappa</a></li>
		<li><a href="ChatBot.jsp">ChatBot</a></li>
		<li><a href="infoapp.jsp">Info App</a></li>
		<li><a href="aboutus.jsp">Chi Siamo</a></li>
		<% } else if(tipoUtente.equals(Tipo.Studente)) { %>
		<li><a href="aula.jsp">Aule</a></li>
		<li><a href="Conversazioni">Conversazioni</a></li>
		<li><a href="mappa.jsp">Mappa</a></li>
		<li><a href="ChatBot.jsp">ChatBot</a></li>
		<li><a href="infoapp.jsp">Info App</a></li>
		<li><a href="aboutus.jsp">Chi Siamo</a></li>
		<% } else if(tipoUtente.equals(Tipo.Docente) || tipoUtente.equals(Tipo.Coordinatore)) { %>
		<li><a href="aula.jsp">Aule</a></li>
		<li><a href="Conversazioni">Conversazioni</a></li>
		<li><a href="mappa.jsp">Mappa</a></li>
		<li><a href="ChatBot.jsp">ChatBot</a></li>
		<li><a href="infoapp.jsp">Info App</a></li>
		<li><a href="aboutus.jsp">Chi Siamo</a></li>
		<% } else if(tipoUtente.equals(Tipo.PersonaleTA)) { %>
		<li><a href="aula.jsp">Aule</a></li>
		<li><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
		<li><a href="mappa.jsp">Mappa</a></li>
		<li><a href="ChatBot.jsp">ChatBot</a></li>
		<li><a href="infoapp.jsp">Info App</a></li>
		<li><a href="aboutus.jsp">Chi Siamo</a></li>
		<% } %>
	</ul>
</div>

<jsp:include page="header.jsp"/>

<div id="chatContainer">
	<h1>Chat Bot</h1>
	<div id="messages"></div>
	<input type="text" id="userMessage" placeholder="Scrivi un messaggio..." />
	<button onclick="sendMessage()">Invia</button>
</div>

<%@ include file="footer.jsp" %>
</body>
</html>
