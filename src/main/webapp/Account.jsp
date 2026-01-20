<%@ page contentType="text/html; charset=UTF-8" pageEncoding="UTF-8" %>
<%@ page import="it.unisa.uniclass.utenti.service.StudenteService" %>
<%@ page import="it.unisa.uniclass.utenti.service.CoordinatoreService" %>
<%@ page import="it.unisa.uniclass.utenti.service.PersonaleTAService" %>
<%@ page import="it.unisa.uniclass.utenti.service.DocenteService" %>
<%@ page import="it.unisa.uniclass.utenti.model.*" %>
<%@ taglib prefix="c" uri="http://java.sun.com/jsp/jstl/core" %>

<%
    HttpSession sessione = request.getSession(true);
    Utente user = (Utente) sessione.getAttribute("currentSessionUser");

    if (user != null) {
        session.setAttribute("utenteEmail", user.getEmail());
    } else {
        response.sendRedirect("Login.jsp");
        return;
    }

    StudenteService studenteService = new StudenteService();
    CoordinatoreService coordinatoreService = new CoordinatoreService();
    DocenteService docenteService = new DocenteService();
    PersonaleTAService personaleTAService = new PersonaleTAService();

    Studente studente = null;
    Docente docente = null;
    Coordinatore coordinatore = null;
    PersonaleTA personaleTA = null;

    Tipo tipoUtente = user.getTipo();

    if (tipoUtente.equals(Tipo.Studente)) {
        studente = studenteService.trovaStudenteEmailUniClass(user.getEmail());
    } else if (tipoUtente.equals(Tipo.Docente)) {
        docente = docenteService.trovaEmailUniClass(user.getEmail());
    } else if (tipoUtente.equals(Tipo.Coordinatore)) {
        coordinatore = coordinatoreService.trovaCoordinatoreEmailUniclass(user.getEmail());
    } else if (tipoUtente.equals(Tipo.PersonaleTA)) {
        personaleTA = personaleTAService.trovaEmail(user.getEmail());
    }
%>

<!DOCTYPE html>
<html lang="it">
<head>
    <title>UniClass Account</title>
    <script src="scripts/sidebar.js" type="text/javascript"></script>
    <link rel="stylesheet" href="styles/headerStyle.css">
    <link rel="stylesheet" href="styles/barraNavigazioneStyle.css">
    <link rel="stylesheet" href="styles/informazioniStyle.css">
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
        <li><a href="aula.jsp">Aule</a></li>
        <li><a href="Conversazioni">Conversazioni</a></li>
        <li><a href="mappa.jsp">Mappa</a></li>
        <li><a href="ChatBot.jsp">ChatBot</a></li>
        <li><a href="infoapp.jsp">Info App</a></li>
        <li><a href="aboutus.jsp">Chi Siamo</a></li>

        <% if (tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <li><a href="PersonaleTA/AttivaUtenti.jsp">Gestione Utenti</a></li>
        <% } %>
    </ul>
</div>

<jsp:include page="header.jsp" />

<%-- ===== SEZIONE INFORMAZIONI ===== --%>

<div class="listaInfo" id="listaInfo">
    <h2>Informazioni</h2>
    <ul id="infolist">

        <% if (tipoUtente.equals(Tipo.Studente)) { %>
        <img src="images/icons/iconstudent.png" alt="Studente">
        <li><c:out value="${studente.nome}"/></li>
        <li><c:out value="${studente.cognome}"/></li>
        <li>Data di nascita: <c:out value="${studente.dataNascita}"/></li>
        <li><c:out value="${studente.matricola}"/></li>
        <li><c:out value="${studente.email}"/></li>
        <li><c:out value="${studente.corsoLaurea.nome}"/></li>
        <li>Data di iscrizione: <c:out value="${studente.iscrizione}"/></li>

        <% } else if (tipoUtente.equals(Tipo.Docente)) { %>
        <img src="images/icons/iconprof.png" alt="Docente">
        <li><c:out value="${docente.nome}"/></li>
        <li><c:out value="${docente.cognome}"/></li>
        <li>Data di nascita: <c:out value="${docente.dataNascita}"/></li>
        <li><c:out value="${docente.matricola}"/></li>
        <li><c:out value="${docente.email}"/></li>
        <li><c:out value="${docente.corsoLaurea.nome}"/></li>
        <li>Data di iscrizione: <c:out value="${docente.iscrizione}"/></li>

        <% } else if (tipoUtente.equals(Tipo.Coordinatore)) { %>
        <img src="images/icons/iconprof.png" alt="Coordinatore">
        <li><c:out value="${coordinatore.nome}"/></li>
        <li><c:out value="${coordinatore.cognome}"/></li>
        <li>Data di nascita: <c:out value="${coordinatore.dataNascita}"/></li>
        <li><c:out value="${coordinatore.matricola}"/></li>
        <li><c:out value="${coordinatore.email}"/></li>
        <li><c:out value="${coordinatore.corsoLaurea.nome}"/></li>
        <li>Iscrizione piattaforma: <c:out value="${coordinatore.iscrizione}"/></li>

        <% } else if (tipoUtente.equals(Tipo.PersonaleTA)) { %>
        <img src="images/icons/iconpersonaleTA.png" alt="Personale TA">
        <li><c:out value="${personaleTA.nome}"/></li>
        <li><c:out value="${personaleTA.cognome}"/></li>
        <li><c:out value="${personaleTA.dataNascita}"/></li>
        <li><c:out value="${personaleTA.id}"/></li>
        <li><c:out value="${personaleTA.email}"/></li>
        <li><c:out value="${personaleTA.telefono}"/></li>
        <% } %>

    </ul>

    <form action="LogoutServlet" method="post">
        <button type="submit" class="logout-button">Logout</button>
    </form>
</div>

</body>
</html>
