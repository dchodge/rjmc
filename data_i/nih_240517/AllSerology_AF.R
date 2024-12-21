library(tidyverse)
library(gtsummary)

setwd("S:/Group/AF_LC_RT_share/NIH Aust HCW Study/Serol_Analysis_AF")

vac_hist <- read_csv("./data/vaccinations.csv", col_types = cols())%>%
  select(pid,year,brand,vaccination_date,status)

prior_vac_counts <- vac_hist %>%
    group_by(pid) %>%
    summarise(
        .groups = "drop",
        prior2020 = sum(year >= 2015 & year < 2020 & (status == "Australia" | status == "Overseas")),
        prior2021 = sum(year >= 2016 & year < 2021 & (status == "Australia" | status == "Overseas")),
        prior2022 = sum(year >= 2017 & year < 2022 & (status == "Australia" | status == "Overseas")),
        prior2023 = sum(year >= 2018 & year < 2023 & (status == "Australia" | status == "Overseas")),
    )

prior_vac_counts_cum <- vac_hist %>%
  group_by(pid) %>%
  summarise(
    .groups = "drop",
    prior2020 = sum(year >= 2015 & year < 2020 & (status == "Australia" | status == "Overseas")),
    prior2021 = sum(year >= 2015 & year < 2021 & (status == "Australia" | status == "Overseas")),
    prior2022 = sum(year >= 2015 & year < 2022 & (status == "Australia" | status == "Overseas")),
    prior2023 = sum(year >= 2015 & year < 2023 & (status == "Australia" | status == "Overseas")),
  )

vax_study_years <- vac_hist %>%
    group_by(pid) %>%
    summarise(
        .groups = "drop",
        vax2020 = sum(status[year == 2020] %in% c("Australia", "Overseas")),
        vax2021 = sum(status[year == 2021] %in% c("Australia", "Overseas")),
        vax2022 = sum(status[year == 2022] %in% c("Australia", "Overseas")),
        vax2023 = sum(status[year == 2023] %in% c("Australia", "Overseas")),
    )

vax2020_pids <- vac_hist %>% filter(year == 2020, (status == "Australia" | status == "Overseas")) %>% pull(pid)
vax2021_pids <- vac_hist %>% filter(year == 2021, (status == "Australia" | status == "Overseas")) %>% pull(pid)
vax2022_pids <- vac_hist %>% filter(year == 2022, (status == "Australia" | status == "Overseas")) %>% pull(pid)
vax2023_pids <- vac_hist %>% filter(year == 2023, (status == "Australia" | status == "Overseas")) %>% pull(pid)

vac_study_year <- read_csv("data/vaccinations.csv", col_types = cols())%>%
  filter(year>2019)
vaccinated <- read_csv("data/participants.csv", col_types = cols())%>%
  left_join(vac_study_year, "pid")

enrolled_vax <- vaccinated %>% filter (year >= recruitment_year)%>%
  select(
    pid = pid, status = status, brand,year = year, vaccination_date
  )

enrolled_vax <- enrolled_vax %>% filter (status != "Unknown") # note Annette removed "CHW-247" in 2022 when they did not participate although they participated in 2020 and 2021)
enrolled_vax$status [enrolled_vax$status == "Australia"] <- "Yes"
table(enrolled_vax$year,enrolled_vax$status)
table(enrolled_vax$year,enrolled_vax$brand)

##following section is not needed - it removes those with unclear vaccination status - but there were in 2020 when there were no flu cases
# status_unclear <- enrolled_vax %>% filter(year == 2020, (pid == "ALF-018" | pid == "QCH-008"))%>% select(pid,year,status)
# status_unclear$status [status_unclear$status == "No"] <- "unclear"
# enrolled_vax <- enrolled_vax %>%
#   left_join(status_unclear, c("pid", "year"))%>% filter(is.na(status.y)) # data set after those with unclear status removed
# table(enrolled_vax$year,enrolled_vax$status.x)

serology <-read_csv("data/serology.csv", col_types = cols()) %>%
  select(pid,year,day,virus,titre,vax_inf,subtype,virus_egg_cell,virus_clade,virus_vaccine)

fun_fix_pids <- function(pid) {
  str_replace(pid, "([[:alpha:]]{3})\\s?-?(\\d{3})", "\\1-\\2") %>%
    toupper() %>%
    recode(
      "JHH-830" = "JHH-082", # NOTE Changed within 2022
      "JHH-835" = "JHH-090", # NOTE Changed within 2023
      "JHH-834" = "JHH-158", # NOTE Changed within 2023
      "JHH-826" = "JHH-297", # NOTE Changed within 2022
      "JHH-304" = "JHH-820", # NOTE Changed within 2022
      "JHH-474" = "JHH-828", # NOTE Changed within 2023
      "JHH-513" = "JHH-832" # NOTE Changed within 2023
    )
}

serology <- serology %>%
  mutate(pid = fun_fix_pids(pid))

lab_record <- read_csv("data/Combined site sera all years HCWFLU Study2.csv")%>%
  select(pid,year,day,vax_inf,bleed_date,Vaccinated)

lab_record <- lab_record %>%
  mutate(pid = fun_fix_pids(pid))

table(lab_record$vax_inf)
table(lab_record$vax_inf,lab_record$year)

#check bleed date versus lab sera records conflicts
bleeds_vax <- read.csv("data/bleed_dates.csv") %>% select(pid,year,day,bleed_date=date) %>%
  left_join(lab_record %>% filter(vax_inf=="V"),c("pid","year","day"))%>% select(pid,year,day,vax_inf,bleed_date_rc=bleed_date.x,bleed_date_lab=bleed_date.y,Vaccinated )
# of 11973 bleed dates records in RedCap 96 lack a bleed-date in the lab records
write.csv(bleeds_vax, "S:/Group/AF_LC_RT_share/NIH Aust HCW Study/Serol_Analysis_AF/bleeds_vax_rcap_v_lab.csv", row.names=FALSE)

bleeds_all <- read.csv("data/bleed_dates.csv") %>% select(pid,year,day,bleed_date=date) %>%
  left_join(lab_record,c("pid","year","day")) %>% select(pid,year,day,vax_inf,bleed_date_rc=bleed_date.x,bleed_date_lab=bleed_date.y,Vaccinated )


titres_all <- serology %>%
  filter(year %in% 2020:2023,subtype %in% c("H1","H3"), day %in% c(0, 14, 220), virus %in% c("A/Brisbane/02/2018e","A/Victoria/2570/2019e","A/Hong Kong/2671/2019e","A/South Australia/34/2019e","A/Darwin/09/2021e","A/Sydney/5/2021","A/Sydney/5/2021e")) %>%
  left_join(read_csv("data/participants.csv", col_types = cols())%>% select(pid,site,gender,age_screening,bmi), "pid") %>%
  left_join(prior_vac_counts, "pid") %>%
  left_join(enrolled_vax, c("pid", "year")) %>% 
  left_join(read_csv("data/2022_2023_Flu_Swabs.csv", col_types = cols())%>% select(pid,year,swab_date=samp_date,infected=Combined_Subtype_result), c("pid", "year"))%>%
  left_join(bleeds_all, c("pid", "year","day","vax_inf")) %>% 
  mutate(
    prior_vax_in_serum_year = case_when(
      year == 2020 ~ prior2020,
      year == 2021 ~ prior2021,
      year == 2022 ~ prior2022,
      year == 2023 ~ prior2023,
    ),
    prior_vax_in_serum_year_cat = case_when(
      prior_vax_in_serum_year == 0 ~ "0",
      prior_vax_in_serum_year %in% 1:2 ~ "1-2",
      prior_vax_in_serum_year %in% 3:5 ~ "3-5",
    ),
    titre_type = if_else(
      (year == 2020 & virus %in% c("A/Brisbane/02/2018e","A/South Australia/34/2019e")) | (year == 2021 & virus %in% c("A/Victoria/2570/2019e","A/Hong Kong/2671/2019e"))|
        (year == 2022 & virus %in% c( "A/Victoria/2570/2019e","A/Darwin/09/2021e"))|(year == 2023 & virus %in% c( "A/Sydney/5/2021e","A/Darwin/09/2021e")),
      "vaccine", "other" 
    ) %>% 
      factor(c("vaccine", "other")),
  ) %>%
  mutate(agegroup = cut(age_screening, c(-Inf, 30, 40, 50, Inf)))%>%
  left_join(vax_study_years, c("pid")) %>%
  group_by(pid) %>%
  mutate(
    v14_2020 = if_else(any(!is.na(titre[day == 14 & year == 2020])), 1L, unique(vax2020)),
    v14_2021 = if_else(any(!is.na(titre[day == 14 & year == 2021])), 1L, unique(vax2021)),
    v14_2022 = if_else(any(!is.na(titre[day == 14 & year == 2022])), 1L, unique(vax2022)),
    v14_2023 = if_else(any(!is.na(titre[day == 14 & year == 2023])), 1L, unique(vax2023)),
    v220_2020 = if_else(any(!is.na(titre[day == 220 & year == 2020])), 1L, unique(vax2020)),
    v220_2021 = if_else(any(!is.na(titre[day == 220 & year == 2021])), 1L, unique(vax2021)),
    v220_2022 = if_else(any(!is.na(titre[day == 220 & year == 2022])), 1L, unique(vax2022)),
    v220_2023 = if_else(any(!is.na(titre[day == 220 & year == 2023])), 1L, unique(vax2023)),
  ) %>%
  ungroup() 
#calculate intervals from dates
titres_all$vaccination_date <- as.Date(titres_all$vaccination_date)
titres_all$bleed_date_rc <- as.Date(titres_all$bleed_date_rc)
titres_all$vax_blood_intervalrc <- titres_all$bleed_date_rc - titres_all$vaccination_date
titres_all$vax_blood_interval <- titres_all$bleed_date_lab - titres_all$vaccination_date
titres_all$vax_inf_interval <- titres_all$swab_date - titres_all$vaccination_date
titres_all$bleed_inf_interval <- titres_all$swab_date - titres_all$bleed_date_lab


write.csv(titres_all, "S:/Group/AF_LC_RT_share/NIH Aust HCW Study/Serol_Analysis_AF/titres_all.csv", row.names=FALSE)


# titres_all$prior_vax_in_serum_year <- as.factor(titres_all$prior_vax_in_serum_year)
# titres_all$status <- as.factor(titres_all$status)
# titres_all$v14_2020 <- as.factor(titres_all$v14_2020)

table_2020 <- titres_all %>% 
  filter(year == 2020, day %in% c(0), subtype == "H1", titre_type == "vaccine") %>%
  select(gender,status,age_screening, prior_vax_in_serum_year_cat,status,vax_blood_interval,vax_blood_intervalrc,brand,v14_2020, v220_2020) %>% 
  tbl_summary(by=prior_vax_in_serum_year_cat,
              missing_text="Missing") %>% 
  add_overall() %>% 
  add_p(list(all_continuous() ~ "kruskal.test", 
             all_categorical() ~ "fisher.test"))
table_2020

table_2020 %>% 
  as_hux_xlsx("table_2020.xlsx")

table_2021 <- titres_all %>% 
  filter(year == 2021, day %in% c(0), subtype == "H1", titre_type == "vaccine") %>%
  select(gender,status,age_screening, prior_vax_in_serum_year_cat,status,brand,v14_2021, v220_2021) %>% 
  tbl_summary(by=prior_vax_in_serum_year_cat,
              missing_text="Missing") %>% 
  add_overall() %>% 
  add_p(list(all_continuous() ~ "kruskal.test", 
             all_categorical() ~ "fisher.test"))
table_2021

table_2021 %>% 
  as_hux_xlsx("table_2021.xlsx")

table_2022 <- titres_all %>% 
  filter(year == 2022, day %in% c(0), subtype == "H1", titre_type == "vaccine") %>%
  select(gender,status,age_screening, prior_vax_in_serum_year_cat,status,brand,v14_2022, v220_2022,infected) %>% 
  tbl_summary(by=prior_vax_in_serum_year_cat,
              missing_text="Missing") %>% 
  add_overall() %>% 
  add_p(list(all_continuous() ~ "kruskal.test", 
             all_categorical() ~ "fisher.test"))
table_2022
table_2022 %>% 
  as_hux_xlsx("table_2022.xlsx")

table_2023 <- titres_all %>% 
  filter(year == 2023, day %in% c(0), subtype == "H1", titre_type == "vaccine") %>%
  select(gender,status,age_screening, prior_vax_in_serum_year_cat,status,brand,v14_2023, v220_2023,infected) %>% 
  tbl_summary(by=prior_vax_in_serum_year_cat,
              missing_text="Missing") %>% 
  add_overall() %>% 
  add_p(list(all_continuous() ~ "kruskal.test", 
             all_categorical() ~ "fisher.test"))
table_2023

table_2023 %>% 
  as_hux_xlsx("table_2023.xlsx")

table_intervals_20 <- titres_all %>% 
  filter(year == 2020,  subtype == "H1", titre_type == "vaccine") %>%
  select(day, prior_vax_in_serum_year_cat,vax_blood_interval) %>% 
  tbl_summary(by=day,
              missing_text="Missing")  
table_intervals_20
table_intervals_20 %>% 
  as_hux_xlsx("table_intervals_20.xlsx")

table_intervals_21 <- titres_all %>% 
  filter(year == 2021,  subtype == "H1", titre_type == "vaccine") %>%
  select(day,vax_blood_interval) %>% 
  tbl_summary(by=day,
              missing_text="Missing") 
table_intervals_21

table_intervals_22 <- titres_all %>% 
  filter(year == 2022,  subtype == "H1", titre_type == "vaccine") %>%
  select(day, vax_blood_interval) %>% 
  tbl_summary(by=day,
              missing_text="Missing")
table_intervals_22

table_intervals_22 <- titres_all %>% 
  filter(year == 2022,  subtype == "H1", titre_type == "vaccine",vax_inf=="V") %>%
  select(day, bleed_inf_interval) %>% 
  tbl_summary(by=day,
              missing_text="Missing")
table_intervals_22

table_intervals_23 <- titres_all %>% 
  filter(year == 2023,  subtype == "H1", titre_type == "vaccine") %>%
  select(day, prior_vax_in_serum_year_cat,vax_blood_interval) %>% 
  tbl_summary(by=day,
              missing_text="Missing") 
table_intervals_23

table_intervals_23 <- titres_all %>% 
  filter(year == 2023,  subtype == "H1", titre_type == "vaccine",vax_inf=="V") %>%
  select(day, vax_inf_interval) %>% 
  tbl_summary(by=day,
              missing_text="Missing")
table_intervals_23

table_intervals_23 <- titres_all %>% 
  filter(year == 2023,  subtype == "H1", titre_type == "vaccine",vax_inf=="V") %>%
  select(day, bleed_inf_interval) %>% 
  tbl_summary(by=day,
              missing_text="Missing")
table_intervals_23

############### ignore code after this point - needs refining

titres$prior_vax_in_serum_year <- as.factor(titres$prior_vax_in_serum_year)
titres$age <- (titres$date_screening-titres$dob)
titres$age <- titres$age/365



#demographics-------
table_participants_2020 <- titres %>% 
    filter (virus == "A/South Australia/34/2019e", year == 2020, day==14) %>%
  select(prior2020,gender,age) %>% 
  tbl_summary(by=prior2020,
              missing_text="Missing") %>% 
  add_p(list(all_continuous() ~ "wilcox.test", 
             all_categorical() ~ "fisher.test"))
table_participants_2020

table_participants_2021 <- titres %>% 
  filter (virus == "A/Hong Kong/2671/2019e", year == 2021, day==14) %>%
  select(prior2021,gender,age) %>% 
  tbl_summary(by=prior2021,
              missing_text="Missing") %>% 
  add_p(list(all_continuous() ~ "wilcox.test", 
             all_categorical() ~ "fisher.test"))
table_participants_2021

summarise_logmean <- function(vec, round_to = 0) {
  vec <- na.omit(vec)
  total <- length(vec)
  log_vec <- log(vec)
  logmean <- mean(log_vec)
  logse <- sd(log_vec) / sqrt(total)
  logmargin <- 1.96 * logse
  loglow <- logmean - logmargin
  loghigh <- logmean + logmargin
  mean <- exp(logmean)
  low <- exp(loglow)
  high <- exp(loghigh)
  tibble(total, mean, low, high)
}

gmts_homologous_pre_post <- titres %>% 
    filter(day %in% c(0, 14), titre_type == "vaccine") %>%
    group_by(year, subtype, day, prior_vax_in_serum_year_cat) %>% 
    summarise(.groups = "drop", summarise_logmean(titre)) %>%
    mutate(timepoint = recode(as.factor(day), "0" = "Pre-vax", "14" = "Post-vax"))

make_gmt_plot <- function(data, filename, width) {
    data %>%
        mutate(subtype_color = if_else(subtype == "H1", "#0066CC", "#CC0066")) %>%
        ggplot(aes(timepoint, mean, ymin = low, ymax = high)) +
        theme_bw() +
        theme(
            panel.grid.minor = element_blank(),
            panel.grid.major.x = element_blank(),
            #legend.position = c(0.75,0.18),
            legend.position = "right",
            strip.background = element_blank(),
            axis.title.x = element_blank(),
            strip.placement = "outside",
            panel.spacing = unit(0, "null"),
        ) +
        facet_wrap(~year, strip.position = "bottom") +
        scale_x_discrete("", expand = expansion(0, 0)) +
        scale_y_log10("Geometric mean titre", breaks = 5 * 2^(0:15)) +
        scale_shape_manual("years vaccinated", values = c(1, 8, 0)) +
        coord_cartesian(ylim = c(5, 1280), xlim = c(0.5, 2.5)) +
        scale_color_identity() +
        geom_pointrange(
            aes(shape = prior_vax_in_serum_year_cat, color = subtype_color), 
            position = position_dodge(width = 0.5)
        ) +
        geom_vline(xintercept = 1.5, color = "gray50")
    ggsave(glue::glue("{filename}.jpg"), width = width, height = 10, units = "cm")
    ggsave(glue::glue("{filename}.pdf"), width = width, height = 10, units = "cm")
}

make_gmt_plot(gmts_homologous_pre_post %>% filter(subtype == "H1"), "Figures/gmt_plot_homologousH1_2020_2023", 15)
make_gmt_plot(gmts_homologous_pre_post %>% filter(subtype == "H3"), "Figures/gmt_plot_homologousH3_2020_2023", 15)
make_gmt_plot(gmts_homologous_pre_post %>% filter(year == 2020), "Figures/gmt_plot_homolH1_H3_2020", 10)
make_gmt_plot(gmts_homologous_pre_post %>% filter(year == 2021), "Figures/gmt_plot_homolH1_H3_2021", 10)

gmts_homologous_post <- titres %>% 
  filter(day %in% c(14), titre_type == "vaccine") %>%
  group_by(prior_vax_in_serum_year_cat, year, subtype) %>%
  summarise(.groups = "drop", summarise_logmean(titre)) 

make_gmt_plot_post <- function(data, filename, width) {
  data %>%
    mutate(subtype_color = if_else(subtype == "H1", "#0066CC", "#CC0066")) %>%
 #   ggplot(aes(subtype, mean, ymin = low, ymax = high)) +
    ggplot(aes(as.factor(year), mean, ymin = low, ymax = high)) +
    theme_bw() +
    theme(
      panel.grid.minor = element_blank(),
      panel.grid.major.x = element_blank(),
      #legend.position = c(0.75,0.18),
      legend.position = "right",
      strip.background = element_blank(),
      axis.title.x = element_blank(),
      strip.placement = "outside",
      panel.spacing = unit(0, "null"),
    ) +
    facet_wrap(~subtype, strip.position = "bottom") +
    scale_x_discrete("", expand = expansion(0, 0)) +
    scale_y_log10("Post-vaccination Geometric Mean Titre", breaks = 5 * 2^(0:15)) +
    scale_shape_manual("years vaccinated", values = c(1, 8, 0)) +
    coord_cartesian(ylim = c(5, 1280), xlim = c(0.5, 3.5)) +
    scale_color_identity() +
    geom_pointrange(
      aes(shape = prior_vax_in_serum_year_cat, color = subtype_color), 
      position = position_dodge(width = 0.5)
    ) 
  ggsave(glue::glue("{filename}.jpg"), width = width, height = 10, units = "cm")
  ggsave(glue::glue("{filename}.pdf"), width = width, height = 10, units = "cm")
}

make_gmt_plot_post(gmts_homologous_post, "Figures/gmt_plot_post", 15)
make_gmt_plot(gmts_homologous_pre_post, "Figures/gmt_plot_homologous", 25)

ratios <- titres %>%
pivot_wider(names_from = "day", values_from = "titre") %>%
mutate(ratio = `14` / `0`, seroconv = as.integer(ratio >= 4))

gmr_homologous_pre_post <- ratios %>%
  filter(titre_type == "vaccine", prior_vax_in_serum_year_cat != "NA") %>%
  group_by(prior_vax_in_serum_year_cat, year, subtype) %>%
  summarise(.groups = "drop", summarise_logmean(ratio))

make_gmr_plot <- function(data, filename, width) {
  data %>%
    mutate(subtype_color = if_else(subtype == "H1", "#0066CC", "#CC0066")) %>%
    ggplot(aes(as.factor(year), mean, ymin = low, ymax = high)) +
    theme_bw() +
    theme(
      panel.grid.minor = element_blank(),
      panel.grid.major.y = element_blank(),
      panel.grid.major.x = element_blank(),
      legend.position = "bottom",
      strip.background = element_blank(),
      axis.title.x = element_blank(),
      strip.placement = "outside",
      panel.spacing = unit(0, "null"),
    ) +
    geom_hline(yintercept = 4, colour = "gray50")+
    #facet_wrap(~year, strip.position = "bottom") +
    scale_x_discrete("", expand = expansion(0, 0)) +
    scale_y_log10("Geometric mean titre rise", breaks = 1 * 2^(0:15)) +
    scale_shape_manual("Prior vaccinations", values = c(1, 8, 0)) +
    coord_cartesian(ylim = c(1, 128), xlim = c(0.5, 4.5)) +
    scale_color_identity() +
    geom_pointrange(
      aes(shape = prior_vax_in_serum_year_cat, color = subtype_color), 
      position = position_dodge(width = 0.5)
    ) 
  ggsave(glue::glue("{filename}.jpg"), width = width, height = 10, units = "cm")
  ggsave(glue::glue("{filename}.pdf"), width = width, height = 10, units = "cm")
} 

make_gmr_plot(gmr_homologous_pre_post %>% filter(subtype == "H1"),"Figures/gmr_homologousH1_2020_2023",10)
make_gmr_plot(gmr_homologous_pre_post %>% filter(subtype == "H3"),"Figures/gmr_homologousH3_2020_2023",10)


summarise_prop <- function(vec) {
    vec <- na.omit(vec)
    success <- sum(vec)
    total <- length(vec)
    ci <- PropCIs::exactci(success, total, 0.95)
    prop <- success / total
    low <- ci$conf.int[[1]]
    high <- ci$conf.int[[2]]
    f <- function(x) round(x * 100)
    tibble(
    prop, low, high,
    comb = glue::glue("{f(prop)}% ({f(low)}%, {f(high)}%)")
    )
}

seroconv_homologous <- ratios %>%
    filter(titre_type == "vaccine") %>%
    group_by(prior_vax_in_serum_year_cat, year, subtype) %>%
    summarise(.groups = "drop", summarise_prop(seroconv))


seroconv_homologous_plot <- seroconv_homologous %>%
    mutate(subtype_color = if_else(subtype == "H1", "#008080", "#ff00ff")) %>%
    ggplot(aes(as.factor(year), prop, ymin = low, ymax = high)) +
    theme_bw() +
    theme(
        panel.grid.minor = element_blank(),
        panel.grid.major.x = element_blank(),
        legend.position = "bottom",
        strip.background = element_blank(),
        axis.title.x = element_blank(),
        strip.placement = "outside",
        panel.spacing = unit(0, "null"),
    ) +
  facet_wrap(~subtype, strip.position = "bottom") +
      scale_y_continuous("Proportion serconverted", breaks = seq(0, 1, 0.1)) +
    scale_shape_manual("Prior vaccinations", values = c(1, 8, 0)) +
    scale_color_identity() +
    coord_cartesian(ylim = c(0, 1)) +
    geom_pointrange(
        aes(shape = prior_vax_in_serum_year_cat, color = subtype_color), 
        position = position_dodge(width = 0.5)
    )
seroconv_homologous_plot

ggsave("extraserology/vaccine_response_plot.pdf", fit_plot, width = 15, height = 10, units = "cm")


seroconv_homologous_Prevax <- ratios %>%
  filter(titre_type == "vaccine",subtype == "H1", year <2022) %>%
  group_by(prior_vax_in_serum_year_cat, Prevax, year) %>%
  summarise(.groups = "drop", summarise_prop(seroconv))


seroconv_homologous_plot <- seroconv_homologous %>%
  filter(subtype == "H1") %>%
  mutate(year_color = if_else(year == "2021", "#6666FF","#008080" )) %>%
  ggplot(aes(prior_vax_in_serum_year_cat, prop, ymin = low, ymax = high)) +
  theme_bw() +
  theme(
    panel.grid.minor = element_blank(),
    panel.grid.major.x = element_blank(),
    legend.position = "bottom",
    strip.background = element_blank(),
    axis.title.x = element_blank(),
    strip.placement = "outside",
    panel.spacing = unit(0, "null"),
  ) +
  facet_wrap(~year, strip.position = "top") +
  scale_y_continuous("Proportion serconverted", breaks = seq(0, 1, 0.1)) +
  scale_shape_manual("Prior vaccinations", values = c(1, 8, 0)) +
  scale_color_identity() +
  coord_cartesian(ylim = c(0, 1)) +
  geom_pointrange(
    aes(shape = prior_vax_in_serum_year_cat, color = year_color), 
    position = position_dodge(width = 0.8)
  )
seroconv_homologous_plot
ggsave("seroconvert_H1_prior.pdf",seroconv_homologous_plot, width = 12, height = 10, units = "cm")

seroconv_homologous_5c <- ratios %>%
  filter(titre_type == "vaccine") %>%
  group_by(prior_vax_in_serum_year, year, subtype) %>%
  summarise(.groups = "drop", summarise_prop(seroconv))

seroconv_homologous_plot_5c <- seroconv_homologous_5c %>%
  mutate(subtype_color = if_else(subtype == "H1", "#008080", "#ff00ff")) %>%
  ggplot(aes(as.factor(year), prop, ymin = low, ymax = high)) +
  theme_bw() +
  theme(
    panel.grid.minor = element_blank(),
    panel.grid.major.x = element_blank(),
    legend.position = "right",
    strip.background = element_blank(),
    axis.title.x = element_blank(),
    strip.placement = "outside",
    panel.spacing = unit(0, "null"),
    axis.text.y = element_text(size = 8),
    axis.title.y = element_text(size = 11),
    axis.text.x = element_text(size = 11),
    
  ) +
  facet_wrap(~subtype, strip.position = "bottom") +
  theme(strip.text = element_text(size = 12))+
  scale_y_continuous("Proportion serconverted", breaks = seq(0, 1, 0.1)) +
  scale_shape_manual("Prior vaccinations", values = c(1, 17, 0, 19,2, 8)) +
  scale_color_identity() +
  coord_cartesian(ylim = c(0, 0.95)) +
  geom_pointrange(
    aes(shape = prior_vax_in_serum_year, color = subtype_color), 
    position = position_dodge(width = 0.8)
  )
seroconv_homologous_plot_5c

ratios %>% count(brand, year)

ratios_fit <- lm(
    I(log(fold)) ~ year * titre_type * brand, 
    titresV %>% mutate(year = as.factor(year))
)

calc_ratios <- function(year, type, brand) {
    names = c("(Intercept)")
    year_not_ref = year != 2020
    type_not_ref = type != "vaccine"
    brand_not_ref = brand != "GSK"
    if (year_not_ref) {
        names[length(names) + 1] = paste0("year", year)
        if (type_not_ref) {
            names[length(names) + 1] = paste0("year", year, ":", "titre_type", type)
            if (brand_not_ref) {
                names[length(names) + 1] = paste0("year", year, ":", "titre_type", type, ":", "brand", brand)
            }
        }
        if (brand_not_ref) {
            names[length(names) + 1] = paste0("year", year, ":", "brand", brand)
        }
    }
    if (type_not_ref) {
        names[length(names) + 1] = paste0("titre_type", type)
        if (brand_not_ref) {
            names[length(names) + 1] = paste0("titre_type", type, ":", "brand", brand)
        }
    }
    if (brand_not_ref) {
        names[length(names) + 1] = paste0("brand", brand)
    }
    stopifnot(all(names %in% names(coef(ratios_fit))))
    stopifnot(all(names %in% colnames(vcov(ratios_fit))))
    stopifnot(all(names %in% rownames(vcov(ratios_fit))))
    tibble(
        logrise = sum(coef(ratios_fit)[names]), 
        variance = sum(vcov(ratios_fit)[names, names]),
        year = year, type = type, brand = brand,
        coefs = paste0(names, collapse = " ")
    )
}

fit_result <- ratios %>% 
    select(year, type = titre_type, brand) %>% 
    distinct() %>%
    filter(!is.na(brand)) %>%
    pmap_dfr(calc_ratios) %>%
    mutate(
        se = sqrt(variance),
        logriselow = logrise - 1.96 * se,
        logrisehigh = logrise + 1.96 * se,
        rise = exp(logrise),
        riselow = exp(logriselow),
        risehigh = exp(logrisehigh),
    )

write_csv(fit_result, "extraserology/vaccine_response_fit.csv")

fit_plot <- fit_result %>%
    ggplot(aes(type, rise, ymin = riselow, ymax = risehigh)) +
    theme_bw() +
    theme(
        panel.grid.minor.x = element_blank(),
        strip.background = element_blank(),
        panel.spacing = unit(0, "null"),
        axis.title.x = element_blank(),
    ) +
    scale_y_continuous("Rise", breaks = 0:15) +
    coord_cartesian(ylim = c(0, 10)) +
    facet_grid(year~brand) +
    geom_hline(yintercept = 1, lty = "11", color = "gray50") +
    geom_pointrange() +
    geom_label(
        aes(x = titre_type, y = 10, label = n), inherit.aes = FALSE, 
        data = ratios %>% count(brand, year, titre_type) %>% filter(!is.na(brand))
    )
fit_plot
ggsave("extraserology/vaccine_response_plot.pdf", fit_plot, width = 15, height = 10, units = "cm")

ratios_age_plot <- titresV %>%
    filter(!is.na(age_screening)) %>%
    group_by(year, titre_type, agegroup) %>%
    summarise(.groups = "drop", summarise_logmean(fold)) %>%
    ggplot(aes(titre_type, mean, ymin = low, ymax = high, color = agegroup)) +
    theme_bw() +
    theme(
        panel.grid.minor.x = element_blank(),
        strip.background = element_blank(),
        panel.spacing = unit(0, "null"),
        axis.title.x = element_blank(),
        legend.position = "bottom",
    ) +
    scale_y_continuous("Rise", breaks = 0:15) +
    scale_color_discrete("Age") +
    coord_cartesian(ylim = c(0, 11)) +
    facet_wrap(~year) +
    geom_hline(yintercept = 1, lty = "11", color = "gray50") +
    geom_pointrange(position = position_dodge(width = 0.5)) #+
    # geom_label(aes(x = titre_type, y = 10, label = total), position = position_dodge(width = 0.5), show.legend = FALSE)
ratios_age_plot
ggsave("extraserology/ratios_age.pdf", width = 20, height = 8, units = "cm")

titresV %>%
    filter(!is.na(vax2020)) %>%
    group_by(year, titre_type, vax2020) %>%
    summarise(.groups = "drop", summarise_logmean(fold)) %>%
    mutate(vax2020 = as.factor(vax2020)) %>%
    ggplot(aes(titre_type, mean, ymin = low, ymax = high, color = vax2020)) +
    theme_bw() +
    theme(
        panel.grid.minor.x = element_blank(),
        strip.background = element_blank(),
        panel.spacing = unit(0, "null"),
        axis.title.x = element_blank(),
        legend.position = "bottom",
    ) +
    scale_y_continuous("Rise", breaks = seq(0, 100, 2)) +
    scale_color_discrete("vax 2020") +
    facet_wrap(~ year) +
    geom_hline(yintercept = 1, lty = "11", color = "gray50") +
    geom_pointrange(position = position_dodge(width = 0.5))

ggsave("extraserology/ratios_vax2020.pdf", width = 15, height = 12, units = "cm")
