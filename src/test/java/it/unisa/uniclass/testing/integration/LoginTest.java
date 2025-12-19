package it.unisa.uniclass.testing.integration;

import org.junit.Test;
import org.junit.Before;
import org.junit.After;

import static org.junit.jupiter.api.Assertions.assertTrue;

import org.openqa.selenium.By;
import org.openqa.selenium.WebDriver;
import org.openqa.selenium.chrome.ChromeDriver;
import org.openqa.selenium.JavascriptExecutor;

import java.util.*;

public class LoginTest {
  private WebDriver driver;
  JavascriptExecutor js;

  @Before
  public void setUp() {
    driver = new ChromeDriver();
    js = (JavascriptExecutor) driver;
  }

  @After
  public void tearDown() {
    driver.quit();
  }

  @Test
  public void tC1ValidLogin() {
    driver.get("http://localhost:8080/UniClass-Dependability/Home");
    driver.findElement(By.cssSelector("span > a > img")).click();
    driver.findElement(By.id("email")).sendKeys("giacomoporetti@unisa.it");
    driver.findElement(By.id("password")).sendKeys("2222WxY$"); // ggignore
    driver.findElement(By.cssSelector(".logreg")).click();

    // Assertion: login valido → pagina contiene indicazione di successo
    assertTrue(driver.getPageSource().contains("success") || driver.getPageSource().contains("Home"));
  }

  @Test
  public void tC2NotPresentPassword() {
    driver.get("http://localhost:8080/UniClass-Dependability/Home");
    driver.findElement(By.cssSelector("span > a > img")).click();
    driver.findElement(By.id("email")).sendKeys("giacomoporetti@unisa.it");
    driver.findElement(By.id("password")).sendKeys(""); // password mancante
    driver.findElement(By.cssSelector(".logreg")).click();

    // Assertion: login fallito → pagina contiene messaggio di errore
    assertTrue(driver.getPageSource().contains("errore") || driver.getPageSource().contains("password"));
  }

  @Test
  public void tC3NotValidPassword() {
    driver.get("http://localhost:8080/UniClass-Dependability/Home");
    driver.findElement(By.cssSelector("span > a > img")).click();
    driver.findElement(By.id("email")).sendKeys("giacomoporetti@unisa.it");
    driver.findElement(By.id("password")).sendKeys("2222WxYS"); // password non valida
    driver.findElement(By.cssSelector(".logreg")).click();

    assertTrue(driver.getPageSource().contains("errore") || driver.getPageSource().contains("non valida"));
  }

  @Test
  public void tC4NotPresentEmail() {
    driver.get("http://localhost:8080/UniClass-Dependability/Home");
    driver.findElement(By.cssSelector("span > a > img")).click();
    driver.findElement(By.id("email")).sendKeys(""); // email mancante
    driver.findElement(By.id("password")).sendKeys("2222WxY$");
    driver.findElement(By.cssSelector(".logreg")).click();

    assertTrue(driver.getPageSource().contains("errore") || driver.getPageSource().contains("email"));
  }

  @Test
  public void tC5formatEmailOnlyValid() {
    driver.get("http://localhost:8080/UniClass-Dependability/Home");
    driver.findElement(By.cssSelector("span > a > img")).click();
    driver.findElement(By.id("email")).sendKeys("giacomo@unisa.it"); // email valida
    driver.findElement(By.id("password")).sendKeys("2212"); // password non valida
    driver.findElement(By.cssSelector(".logreg")).click();

    assertTrue(driver.getPageSource().contains("errore") || driver.getPageSource().contains("password"));
  }

  @Test
  public void tC6formatPasswordOnlyValid() {
    driver.get("http://localhost:8080/UniClass-Dependability/Home");
    driver.findElement(By.cssSelector("span > a > img")).click();
    driver.findElement(By.id("email")).sendKeys("giacunsa.it"); // email non valida
    driver.findElement(By.id("password")).sendKeys("2212XyA$"); // password valida
    driver.findElement(By.cssSelector(".logreg")).click();

    assertTrue(driver.getPageSource().contains("errore") || driver.getPageSource().contains("email"));
  }

  @Test
  public void tC7NothingValid() {
    driver.get("http://localhost:8080/UniClass-Dependability/Home");
    driver.findElement(By.cssSelector("span > a > img")).click();
    driver.findElement(By.id("email")).sendKeys("giacunsa.it"); // email non valida
    driver.findElement(By.id("password")).sendKeys("221"); // password non valida
    driver.findElement(By.cssSelector(".logreg")).click();

    assertTrue(driver.getPageSource().contains("errore") || driver.getPageSource().contains("non valido"));
  }
}
